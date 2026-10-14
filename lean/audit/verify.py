#!/usr/bin/env python3
"""Rebuild every proof module and verify the theorem's kernel dependencies."""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
THEOREM = "IV01.twoCheckerVertices"
EXPECTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
AXIOMS_SOURCE = "import IV01\n\n#print axioms IV01.twoCheckerVertices\n"
SOURCE_BINDINGS_PATH = "audit/source-bindings.json"
SOURCE_BINDINGS_SHA256 = "ffc41f51840dabb3cd55829e255890a9a1855cf398252959efcb8a16447b65eb"
# Keep the definitions and the complete theorem declaration and proof fixed.
FIXED_SOURCE_HASHES = {
    "IV01/Definitions.lean":
        "6c3a7fe6abfd4e5866b313fab437431c421c64cb47b79e242a22c07c21004587",
    "IV01/Statement.lean":
        "fdd0cac16eeaed5ded0d1a8c7cd12db78161f47984035a38d1b250181d1812b6",
}
CONFIGURATION_HASHES = {
    "lakefile.toml":
        "412cbd78dfbf8f336a333c50206bdcef68378d4595b1fbead2af45ca8fdd321e",
    "lean-toolchain":
        "8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88",
    "lake-manifest.json":
        "2db9b7be01ae5e338abd01a8dae0d36cb45801b7b44421041ce4257b801628a2",
}
REQUIRED_SOURCES = frozenset({
    "IV01.lean", "IV01/Definitions.lean", "IV01/Statement.lean", "audit/Axioms.lean",
})
MODULE_PATH = re.compile(r"IV01(?:/[A-Za-z][A-Za-z0-9_]*)*\.lean\Z")
SHA256 = re.compile(r"[0-9a-f]{64}\Z")
# Deliberately include comments, strings, and quoted identifiers in this check.
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|axiom|unsafe|native_decide|implemented_by|ofReduceBool)\b"
)
AXIOMS_OUTPUT = re.compile(
    r"\s*'IV01\.twoCheckerVertices' depends on axioms: \[([^\[\]\r\n]*)\]\s*\Z"
)


class AuditError(Exception):
    """A verification condition failed."""


def require(condition, message):
    if not condition:
        raise AuditError(message)


def reject_forbidden(source, name):
    match = FORBIDDEN.search(source)
    require(match is None, f"Disallowed proof token in {name}: "
            f"{match.group(0) if match else ''}")


def check_configuration(root):
    """Bind the build to this source directory and the locked dependencies."""
    snapshot = {}
    for name, expected in CONFIGURATION_HASHES.items():
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"Missing or linked configuration: {name}")
        data = path.read_bytes()
        require(hashlib.sha256(data).hexdigest() == expected, f"Build configuration changed: {name}")
        snapshot[name] = data
    return snapshot


def check_source_bindings(root):
    """Check the immutable source manifest and return its complete inventory."""
    path = root / SOURCE_BINDINGS_PATH
    require(path.is_file() and not path.is_symlink(), "Missing or linked source binding")
    data = path.read_bytes()
    require(hashlib.sha256(data).hexdigest() == SOURCE_BINDINGS_SHA256,
            "Source-binding manifest does not match its SHA256 pin")

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"Duplicate source-binding field: {key}")
            result[key] = value
        return result

    try:
        binding = json.loads(data.decode("utf-8"), object_pairs_hook=unique_object)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditError("Malformed source-binding manifest") from error
    require(isinstance(binding, dict) and set(binding) == {
        "schema", "source_hashes",
    }, "Unexpected source-binding fields")
    require(type(binding["schema"]) is int and binding["schema"] == 1,
            "Unsupported source-binding schema")
    sources = binding["source_hashes"]
    require(isinstance(sources, dict) and sources, "Missing source inventory")
    for name, digest in sources.items():
        require(isinstance(name, str) and MODULE_PATH.fullmatch(name) is not None,
                f"Invalid bound source path: {name}")
        require(isinstance(digest, str) and SHA256.fullmatch(digest) is not None,
                f"Invalid source digest: {name}")
    return sources


def source_paths(root):
    """Enumerate recursively; dependencies are the sole source-tree exclusion."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), "Invalid project directory")
    found = []

    def walk_error(error):
        raise AuditError(f"Cannot enumerate project sources: {error}")

    for current, directories, files in os.walk(root, onerror=walk_error, followlinks=False):
        current = Path(current)
        if current == root:
            directories[:] = [name for name in directories if name not in {".lake", ".git"}]
            files = [name for name in files if name != ".git"]
        for name in directories + files:
            path = current / name
            require(not path.is_symlink(), f"Project symlink is not allowed: {path.relative_to(root)}")
        for name in files:
            if name.endswith(".lean"):
                path = current / name
                require(path.is_file(), f"Lean source is not a regular file: {path.relative_to(root)}")
                found.append(path)
    return sorted(found)


def check_sources(root):
    """Check all Lean sources and return their bytes for a later stability check."""
    source_hashes = check_source_bindings(root)
    snapshot = {}
    for path in source_paths(root):
        name = path.relative_to(root).as_posix()
        require(name == "audit/Axioms.lean" or MODULE_PATH.fullmatch(name) is not None,
                f"Unexpected Lean source: {name}")
        data = path.read_bytes()
        try:
            source = data.decode("utf-8")
        except UnicodeDecodeError as error:
            raise AuditError(f"Lean source is not UTF-8: {name}") from error
        reject_forbidden(source, name)
        snapshot[name] = data
    require(REQUIRED_SOURCES <= snapshot.keys(),
            f"Missing required Lean sources: {sorted(REQUIRED_SOURCES - snapshot.keys())}")
    expected_sources = source_hashes.keys() | {"audit/Axioms.lean"}
    require(snapshot.keys() == expected_sources,
            f"Source inventory differs from its binding: "
            f"missing {sorted(expected_sources - snapshot.keys())}; "
            f"extra {sorted(snapshot.keys() - expected_sources)}")
    for name, expected in source_hashes.items():
        require(hashlib.sha256(snapshot[name]).hexdigest() == expected,
                f"Bound source changed: {name}")
    for name, expected in FIXED_SOURCE_HASHES.items():
        actual = hashlib.sha256(snapshot[name]).hexdigest()
        require(actual == expected, f"Fixed theorem source changed: {name}")
    require(snapshot["audit/Axioms.lean"] == AXIOMS_SOURCE.encode("utf-8"),
            "The axiom-printing source changed")
    return snapshot


def parse_axioms(stdout, stderr=""):
    require(not stderr, "Unexpected standard error from the axiom check")
    match = AXIOMS_OUTPUT.fullmatch(stdout)
    require(match is not None, "Missing, malformed, or additional axiom output")
    names = [name.strip() for name in match.group(1).split(",")]
    require(len(names) == len(EXPECTED_AXIOMS) and set(names) == EXPECTED_AXIOMS,
            f"Unexpected axiom list: {names}")
    return frozenset(names)


def run_checked(command, root):
    print("+ " + " ".join(command), flush=True)
    try:
        result = subprocess.run(command, cwd=root, text=True, encoding="utf-8",
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    except (OSError, UnicodeError) as error:
        raise AuditError(f"Could not execute {command[0]}: {error}") from error
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.stderr:
        print(result.stderr, end="", file=sys.stderr, flush=True)
    require(result.returncode == 0,
            f"Command failed with status {result.returncode}: {' '.join(command)}")
    return result


def verify(root=ROOT):
    root = Path(root)
    configuration_before = check_configuration(root)
    before = check_sources(root)
    modules = sorted(name[:-5].replace("/", ".") for name in before
                     if name != "audit/Axioms.lean")
    # Naming the package preserves the downloaded dependency cache.
    run_checked(["lake", "clean", "iv01"], root)
    run_checked(["lake", "build", *modules], root)
    result = run_checked(["lake", "env", "lean", "audit/Axioms.lean"], root)
    parse_axioms(result.stdout, result.stderr)
    require(check_sources(root) == before, "Lean sources changed during verification")
    require(check_configuration(root) == configuration_before,
            "Build configuration changed during verification")
    print(f"PASS: rebuilt {len(modules)} proof modules; all project Lean sources checked.")
    print("PASS: complete source inventory and SHA256 binding match.")
    print(f"PASS: {THEOREM} uses exactly propext, Classical.choice, Quot.sound.")


def main():
    try:
        verify()
    except (AuditError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
