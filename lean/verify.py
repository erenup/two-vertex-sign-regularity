#!/usr/bin/env python3
"""Build the pinned theorem in fresh objects and record its transitive axioms."""

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("source_audit", ROOT / "audit/verify.py")
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
LEAN_COMMIT = "6a10ac8c22beadecabdbb0919c2b50214762f91d"
BASE_ENV = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_CONFIG_SYSTEM": "/dev/null", "GIT_OPTIONAL_LOCKS": "0",
            "OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"}
GIT = ["/usr/bin/git", "--no-optional-locks", "-c", "core.fsmonitor=false"]
require = audit.require


def utc_now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2) + "\n").encode("utf-8")


def run(command, cwd=ROOT, env=None, log=None):
    try:
        result = subprocess.run(command, cwd=cwd, env=BASE_ENV if env is None else env,
                                capture_output=True, text=True, encoding="utf-8",
                                timeout=1800, check=False)
    except (OSError, UnicodeError, subprocess.TimeoutExpired) as error:
        raise audit.AuditError(f"Command could not finish: {command[0]}") from error
    if log is not None:
        Path(str(log) + ".stdout").write_text(result.stdout, encoding="utf-8")
        Path(str(log) + ".stderr").write_text(result.stderr, encoding="utf-8")
    require(result.returncode == 0, f"Command failed ({result.returncode}): {command[0]}")
    return result


def resolve_compiler():
    lake_name = shutil.which("lake")
    require(lake_name is not None, "Lake is unavailable on PATH")
    lake = Path(lake_name).absolute()
    env = dict(BASE_ENV)
    env["PATH"] = str(lake.parent) + os.pathsep + os.defpath
    for name in ["HOME", "ELAN_HOME"]:
        if name in os.environ:
            env[name] = os.environ[name]
    result = run([str(lake), "--no-build", "env", "lean", "--print-prefix"], env=env)
    require(not result.stderr, "Unexpected Lake resolver diagnostics")
    lines = result.stdout.splitlines()
    require(len(lines) == 1 and lines[0] == lines[0].strip(), "Invalid compiler prefix")
    prefix = Path(lines[0])
    require(prefix.is_absolute(), "Compiler prefix must be absolute")
    lean = (prefix / "bin/lean").resolve(strict=True)
    require(sha(lean) == LEAN_SHA256, "Compiler digest differs from the pin")
    return lean


def artifacts(root, allow_internal_links=False):
    hashes = {}
    root = root.resolve(strict=True)
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            require(allow_internal_links and path.is_file()
                    and path.resolve().is_relative_to(root), "Unsupported linked library artifact")
        if path.is_file():
            name = path.relative_to(root).as_posix()
            require(not name.startswith(("IV01/", "IV01.")), "Theorem module shadows a dependency")
            hashes[name] = {"sha256": sha(path),
                            "symlink": str(path.readlink()) if path.is_symlink() else None}
    return hashes


def dependencies(lean):
    require(sha(lean) == LEAN_SHA256, "Compiler digest differs from the pin")
    version = run([str(lean), "--version"]).stdout.strip()
    require("4.34.0-rc2" in version and LEAN_COMMIT in version, "Compiler version differs")
    toolchain = artifacts(lean.parent.parent / "lib", allow_internal_links=True)
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages, libraries = {}, []
    for entry in manifest["packages"]:
        path = (ROOT / ".lake/packages" / entry["name"]).resolve(strict=True)
        revision = run([*GIT, "rev-parse", "HEAD"], cwd=path).stdout.strip()
        require(revision == entry["rev"], "Dependency revision differs: " + entry["name"])
        require(not run([*GIT, "status", "--porcelain", "--untracked-files=no"], cwd=path).stdout,
                "Dependency tracked sources changed: " + entry["name"])
        library = path / ".lake/build/lib/lean"
        files = {}
        if library.is_dir():
            libraries.append(library)
            files = artifacts(library)
        packages[entry["name"]] = {"revision": revision, "files": files}
    return {"compiler_sha256": LEAN_SHA256, "compiler_version": version,
            "toolchain_library_artifacts": toolchain, "packages": packages}, libraries


def module_order(sources):
    modules = {name[:-5].replace("/", "."): data.decode("utf-8")
               for name, data in sources.items() if name != "audit/Axioms.lean"}
    active, done, ordered = set(), set(), []

    def visit(module):
        require(module in modules, "Missing local module: " + module)
        require(module not in active, "Circular local imports: " + module)
        if module in done:
            return
        active.add(module)
        for line in modules[module].splitlines():
            match = re.match(r"\s*(?:(?:public|private)\s+)?import\s+(.+)", line)
            if match:
                for imported in match.group(1).split("--", 1)[0].split():
                    if imported == "IV01" or imported.startswith("IV01."):
                        visit(imported)
        active.remove(module)
        done.add(module)
        ordered.append(module)

    for module in sorted(modules):
        visit(module)
    return ordered


def prepare_output(path, lean):
    path = Path(path).absolute()
    require(not path.exists() and not path.is_symlink(), "Output directory already exists")
    require(not any(p.is_symlink() for p in path.parents), "Output parent is linked")
    path = path.resolve(strict=False)
    require(not path.is_relative_to(ROOT / ".lake"), "Output overlaps Lake files")
    require(not path.is_relative_to(lean.parent.parent), "Output overlaps installed compiler")
    for dependency in (ROOT / ".lake/packages").iterdir():
        require(not path.is_relative_to(dependency.resolve()), "Output overlaps a dependency")
    path.mkdir(parents=True)
    (path / "objects").mkdir()
    return path


def helpers():
    names = ["verify.py", "audit/verify.py", "audit/test_verify.py"]
    for name in names:
        require((ROOT / name).is_file() and not (ROOT / name).is_symlink(), "Missing or linked helper")
    return {name: sha(ROOT / name) for name in names}


def verify(output):
    started_utc, started = utc_now(), time.monotonic()
    sources = audit.check_sources(ROOT)
    config = audit.check_configuration(ROOT)
    helper_hashes = helpers()
    lean = resolve_compiler()
    output = prepare_output(output, lean)
    print("Verification started UTC: " + started_utc, flush=True)
    print("Source manifest SHA256: " + audit.SOURCE_BINDINGS_SHA256, flush=True)
    print("Snapshotting pinned dependency revisions and library bytes.", flush=True)
    before, libraries = dependencies(lean)
    (output / "DEPENDENCIES.json").write_bytes(json_bytes(before))
    print(before["compiler_version"], flush=True)
    print("Dependencies: all 9 pinned Git revisions; tracked sources clean.", flush=True)
    objects = output / "objects"
    env = dict(BASE_ENV)
    env.update({"PATH": str(lean.parent) + os.pathsep + os.defpath,
                "LEAN_PATH": os.pathsep.join(map(str, [objects, *libraries])),
                "LEAN_NUM_THREADS": "1"})
    runs = []
    for module in module_order(sources):
        name = module.replace(".", "/")
        target = objects / (name + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), "-j1", "-M12288", "-o", str(target), name + ".lean"]
        begin = time.monotonic()
        result = run(command, env=env, log=output / module)
        require(not result.stderr, "Unexpected compiler standard error: " + module)
        require(target.is_file() and target.stat().st_size > 0, "Compiled object missing: " + module)
        runs.append({"module": module, "object_sha256": sha(target), "returncode": 0,
                     "seconds": round(time.monotonic() - begin, 3),
                     "stdout_sha256": hashlib.sha256(result.stdout.encode()).hexdigest(),
                     "stderr_sha256": hashlib.sha256(result.stderr.encode()).hexdigest()})
        print("PASS compiled " + module + " (-j1 -M12288; fresh object)", flush=True)
    result = run([str(lean), "-j1", "-M12288", "audit/Axioms.lean"],
                 env=env, log=output / "AXIOMS")
    axioms = sorted(audit.parse_axioms(result.stdout, result.stderr))
    print(result.stdout, end="", flush=True)
    require(audit.check_sources(ROOT) == sources, "Lean source changed during compilation")
    require(audit.check_configuration(ROOT) == config, "Configuration changed during compilation")
    require(helpers() == helper_hashes, "Verification helper changed during compilation")
    require(resolve_compiler() == lean, "Compiler resolver changed during compilation")
    print("Checking dependency libraries remained byte-identical.", flush=True)
    after, after_libraries = dependencies(lean)
    require(before == after and libraries == after_libraries, "Dependency changed during compilation")
    ended_utc = utc_now()
    summary = {"compiler_sha256": LEAN_SHA256, "compiler_version": before["compiler_version"],
               "dependency_snapshot_sha256": sha(output / "DEPENDENCIES.json"),
               "toolchain_library_artifact_count": len(before["toolchain_library_artifacts"]),
               "packages": {name: {"revision": data["revision"], "library_artifact_count": len(data["files"]),
                                    "artifact_hashes_sha256": hashlib.sha256(json_bytes(data["files"])).hexdigest()}
                            for name, data in before["packages"].items()}}
    (output / "DEPENDENCY_SUMMARY.json").write_bytes(json_bytes(summary))
    receipt = {"status": "PASS", "started_utc": started_utc, "finished_utc": ended_utc,
               "theorem": audit.THEOREM, "axioms": axioms, "build_mode": "fresh project objects",
               "project_objects_initially_empty": True, "dependencies_byte_identical": True,
               "source_manifest_sha256": audit.SOURCE_BINDINGS_SHA256,
               "configuration_sha256": {name: hashlib.sha256(data).hexdigest() for name, data in config.items()},
               "helpers_sha256": helper_hashes, "dependency_summary_sha256": sha(output / "DEPENDENCY_SUMMARY.json"),
               "modules": runs, "seconds": round(time.monotonic() - started, 3)}
    (output / "BUILD_RECEIPT.json").write_bytes(json_bytes(receipt))
    print(f"PASS: {len(runs)} production modules freshly compiled; fixed source inventory unchanged.", flush=True)
    print("PASS: transitive axioms exactly propext, Classical.choice, Quot.sound.", flush=True)
    print("PASS: compiler, pinned dependencies, configuration and helpers unchanged.", flush=True)
    print("Verification finished UTC: " + ended_utc, flush=True)
    return receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / ".audit-build",
                        help="new, nonexistent output directory")
    arguments = parser.parse_args()
    try:
        verify(arguments.output)
    except (audit.AuditError, OSError, ValueError, KeyError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
