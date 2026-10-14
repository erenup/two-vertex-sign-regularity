#!/usr/bin/env python3
"""Check proof bindings, exact output hashes, and negative controls in three modes."""
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MODES = [('normal', [], '1'), ('optimized', ['-O'], '1'), ('hash-seed', [], '8675309')]
MATH_INTEGER = {'ceil', 'comb', 'factorial', 'floor', 'gcd', 'isqrt', 'lcm', 'perm', 'prod', 'trunc'}
FORBIDDEN_CALLS = {'float', 'complex', 'eval', 'exec', 'compile', '__import__', 'getattr'}
FORBIDDEN_MODULES = {'cmath', 'decimal', 'random', 'statistics', 'importlib'}


def need(ok, message):
    if not ok:
        raise SystemExit('FAIL: '+message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def reject_number(value):
    raise SystemExit('FAIL: non-integer JSON number: '+value)


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def read_json(data):
    return json.loads(data, object_pairs_hook=unique_pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def proof_inventory():
    root = HERE.parent/'proofs'
    need(root.is_dir() and not root.is_symlink(), 'invalid proof directory')
    paths = list(root.iterdir())
    need({p.name for p in paths} == {'PROOF.md', 'STATEMENT.md'}, 'proof coverage')
    need(all(p.is_file() and not p.is_symlink() for p in paths), 'invalid proof file')
    return {p.name: digest(p.read_bytes()) for p in paths}


def validate_bindings(data):
    registered = {}
    for line in data.decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 3 and all(re.fullmatch('[0-9a-f]{64}', s) for s in parts[:2]),
             'source binding syntax')
        source, included, name = parts
        need(name not in registered, 'duplicate proof binding')
        registered[name] = included
    need(registered == proof_inventory(), 'proof binding mismatch')
    return registered


def validate_controls(data, registry):
    controls = read_json(data)
    need(type(controls) is dict and set(controls) == set(registry), 'negative-control coverage')
    for name, entries in controls.items():
        need(type(entries) is list and bool(entries), 'missing negative controls: '+name)
        seen = set()
        for entry in entries:
            need(type(entry) is dict and set(entry) == {'name', 'stderr'}, 'negative-control fields')
            label, error = entry['name'], entry['stderr']
            need(type(label) is str and re.fullmatch('[a-z][a-z0-9_-]*', label) is not None,
                 'negative-control name')
            need(label not in seen, 'duplicate negative control')
            seen.add(label)
            need(type(error) is str and bool(error.strip()) and error.endswith('\n'),
                 'negative-control expected error')
    return controls


def inventory():
    files = {}
    for path in HERE.rglob('*'):
        need(not path.is_symlink(), 'symbolic link: '+str(path.relative_to(HERE)))
        if path.is_file():
            name = path.relative_to(HERE).as_posix()
            need('__pycache__' not in path.parts and not name.endswith('.pyc'), 'cache file: '+name)
            need(path.stat().st_size <= 4500000, 'file size: '+name)
            files[name] = path.read_bytes()
    return files


def validate_directory():
    files = inventory()
    need('SHA256SUMS' in files and 'CHECKERS.txt' in files, 'missing manifest or registry')
    sums = {}
    for line in files['SHA256SUMS'].decode().splitlines():
        parts = line.split('  ', 1)
        need(len(parts) == 2 and re.fullmatch('[0-9a-f]{64}', parts[0]) is not None, 'manifest syntax')
        sha, name = parts
        need(name not in sums, 'duplicate manifest entry')
        sums[name] = sha
    need(set(sums) == set(files)-{'SHA256SUMS'}, 'manifest coverage')
    for name, sha in sums.items():
        need(digest(files[name]) == sha, 'manifest mismatch: '+name)
    registry = {}
    for line in files['CHECKERS.txt'].decode().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        parts = line.split()
        need(len(parts) == 2 and re.fullmatch(r'check_[a-z0-9_]+\.py', parts[0]) is not None
             and re.fullmatch('[0-9a-f]{64}', parts[1]) is not None, 'registry syntax')
        name, sha = parts
        need(name not in registry, 'duplicate checker')
        registry[name] = sha
    python_files = {name for name in files if name.endswith('.py')}
    need(all('/' not in name for name in python_files), 'Python file below top level')
    need(bool(registry) and set(registry) == {n for n in python_files if n.startswith('check_')}, 'registry coverage')
    modules = {Path(n).stem for n in python_files}
    need(not (modules & sys.stdlib_module_names), 'standard-library module shadow')
    used = set()
    for name in sorted(python_files):
        tree = ast.parse(files[name].decode(), filename=name)
        for node in ast.walk(tree):
            need(not isinstance(node, ast.Assert), 'assert in '+name)
            if isinstance(node, ast.ImportFrom):
                need(node.level == 0 and node.module, 'relative import in '+name)
                roots = [node.module.split('.')[0]]
                if node.module == 'math':
                    need(all(n.name in MATH_INTEGER for n in node.names), 'non-integer math import')
            elif isinstance(node, ast.Import):
                roots = [n.name.split('.')[0] for n in node.names]
            else:
                roots = []
            for root in roots:
                need(root in sys.stdlib_module_names | modules, 'nonstandard import in '+name)
                need(root not in FORBIDDEN_MODULES, 'inexact or dynamic module in '+name)
                if name != 'run.py':
                    need(root not in {'subprocess', 'multiprocessing', 'concurrent'}, 'checker process import')
                    used.add(root)
            need(not (isinstance(node, ast.Constant) and type(node.value).__name__ in {'float', 'complex'}), 'inexact literal in '+name)
            if isinstance(node, ast.Call):
                if isinstance(node.func, ast.Name):
                    need(node.func.id not in FORBIDDEN_CALLS, 'inexact or dynamic call in '+name)
                if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and node.func.value.id == 'math':
                    need(node.func.attr in MATH_INTEGER, 'non-integer math call')
    helpers = modules-{'run'}-{Path(n).stem for n in registry}
    need(helpers <= used, 'unused arithmetic module')
    for name, data in files.items():
        if name.endswith('.json'):
            read_json(data)
    proofs = validate_bindings(files['SOURCE_BINDINGS.txt'])
    controls = validate_controls(files['NEGATIVE_CONTROLS.json'], registry)
    return registry, controls, proofs, {name: digest(data) for name, data in files.items()}


def execute(command, env, label):
    try:
        return subprocess.run(command, cwd=HERE, env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=600)
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: checker timeout: '+label)


def main():
    registry, controls, proofs, before = validate_directory()
    negative_runs = 0
    for name, expected in sorted(registry.items()):
        previous = None
        for mode, flags, seed in MODES:
            command = [sys.executable, '-S', '-s', '-B']+flags+[str(HERE/name)]
            env = {'PATH': os.defpath, 'LC_ALL': 'C.UTF-8', 'PYTHONHASHSEED': seed}
            result = execute(command, env, name+' '+mode)
            need(result.returncode == 0, 'checker exit status: '+name+' '+mode)
            need(not result.stderr, 'checker standard error: '+name+' '+mode)
            need(digest(result.stdout) == expected, 'output hash mismatch: '+name+' '+mode)
            need(previous is None or previous == result.stdout, 'mode mismatch: '+name)
            previous = result.stdout
            for control in controls[name]:
                label = name+' '+mode+' '+control['name']
                result = execute(command+['--negative-control', control['name']], env, label)
                need(result.returncode == 1, 'negative-control exit status: '+label)
                need(not result.stdout, 'negative-control standard output: '+label)
                need(result.stderr == control['stderr'].encode(), 'negative-control error: '+label)
                negative_runs += 1
        print('PASS: '+name+' (normal, optimized, hash-seed)')
    after = {name: digest(data) for name, data in inventory().items()}
    need(after == before, 'verification files changed during execution')
    need(proof_inventory() == proofs, 'proof files changed during execution')
    print('PASS: '+str(negative_runs)+' negative-control runs; 2 proof bindings')
    print('RESULT: PASS IV-01 verification')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, SyntaxError, UnicodeError) as error:
        raise SystemExit('FAIL: verification input: '+type(error).__name__)
