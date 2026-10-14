#!/usr/bin/env python3
"""Run the exact supporting checks and their rejection controls."""
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MODES = [('normal', [], '1'), ('optimized', ['-O'], '1'),
         ('hash-seed', [], '8675309')]
CHILD = 'core/verification/run.py'
CHILD_MANIFEST = 'core/verification/SHA256SUMS'
PAPER = 'paper/check_examples.py'
CHILD_SHA256 = 'b68cf15d34118d129d1d404291ad3119ac4dbdd1f6738256cd920d848f3c9fc4'
CHILD_MANIFEST_SHA256 = '88bc7968bd6f14b4a0255d17ce0ced07c3c986b5d1020c90158cd1c41ce5bd08'
CHILD_STDOUT_SHA256 = '3a7c0c7328c2e4049743df948ed196aab6afdc18a09421809c172d86640404b7'
PAPER_SHA256 = '4071c6142a2b1639e4fe9a7099ae542663162284b960285ca2a8ffba6ac229bb'
PAPER_STDOUT_SHA256 = 'e90bb2e9c7672585508dfc2dd15094ab8aa9132426fbf713b33bedf51d6705cb'
CONTROL_ERRORS = {'singular': b'FAIL: singular-example bad minor\n', 'signature': b'FAIL: different-signature determinants\n', 'ordinary': b'FAIL: ordinary-corner bad minor\n', 'degenerate': b'FAIL: seed zero-minor pattern\n'}
EXPECTED_FILES = frozenset(['README.md', 'SHA256SUMS', 'core/proofs/PROOF.md', 'core/proofs/STATEMENT.md', 'core/verification/CHECKERS.txt', 'core/verification/NEGATIVE_CONTROLS.json', 'core/verification/README.md', 'core/verification/SHA256SUMS', 'core/verification/SOURCE_BINDINGS.txt', 'core/verification/check_fekete_and_corners.py', 'core/verification/check_schur_and_rank.py', 'core/verification/fixtures/cauchy6_boundary.json', 'core/verification/run.py', 'run.py'])


def need(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def inventory():
    files = {}
    for path in HERE.rglob('*'):
        name = path.relative_to(HERE).as_posix()
        need(not path.is_symlink(), 'symbolic link: ' + name)
        if path.is_file():
            need(path.stat().st_size <= 4500000, 'file size: ' + name)
            files[name] = path.read_bytes()
    return files


def validate(files, paper):
    need(set(files) == EXPECTED_FILES, 'verification file coverage')
    manifest = {}
    for line in files['SHA256SUMS'].decode().splitlines():
        parts = line.split('  ', 1)
        need(len(parts) == 2 and re.fullmatch('[0-9a-f]{64}', parts[0]),
             'manifest syntax')
        sha, name = parts
        need(name not in manifest, 'duplicate manifest entry')
        manifest[name] = sha
    need(set(manifest) == set(files) - {'SHA256SUMS'}, 'manifest coverage')
    for name, sha in manifest.items():
        need(digest(files[name]) == sha, 'manifest mismatch: ' + name)
    need(digest(files[CHILD]) == CHILD_SHA256, 'child runner binding')
    need(digest(files[CHILD_MANIFEST]) == CHILD_MANIFEST_SHA256,
         'child manifest binding')
    need(digest(paper) == PAPER_SHA256, 'paper checker binding')


def read_paper():
    path = ROOT / PAPER
    need(path.parent.is_dir() and not path.parent.is_symlink(),
         'paper directory')
    need(path.is_file() and not path.is_symlink(), 'paper checker file')
    return path.read_bytes()


def execute(command, seed, label):
    try:
        return subprocess.run(command, cwd=ROOT, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=900,
                              env={'PATH': os.defpath, 'LC_ALL': 'C.UTF-8',
                                   'PYTHONHASHSEED': seed})
    except subprocess.TimeoutExpired:
        raise SystemExit('FAIL: timeout: ' + label)


def validate_result(status, stdout, stderr, expected):
    need(status == 0, 'child exit status')
    need(not stderr, 'child standard error')
    need(digest(stdout) == expected, 'child standard output')


def regenerated_manifest(files):
    result = dict(files)
    result['SHA256SUMS'] = ''.join(
        digest(data) + '  ' + name + '\n'
        for name, data in sorted(result.items()) if name != 'SHA256SUMS'
    ).encode()
    return result


def integrity_controls(files, paper):
    cases = []
    changed = dict(files)
    changed[CHILD] += b'\n# changed bytes\n'
    cases.append((changed, paper, 'manifest mismatch: ' + CHILD))
    cases.append((regenerated_manifest(changed), paper, 'child runner binding'))
    changed = dict(files)
    changed[CHILD_MANIFEST] += b'\n'
    cases.append((regenerated_manifest(changed), paper, 'child manifest binding'))
    missing = dict(files)
    del missing[CHILD]
    cases.append((missing, paper, 'verification file coverage'))
    extra = dict(files)
    extra['unregistered.txt'] = b'extra\n'
    cases.append((extra, paper, 'verification file coverage'))
    duplicate = dict(files)
    duplicate['SHA256SUMS'] += files['SHA256SUMS'].splitlines(keepends=True)[0]
    cases.append((duplicate, paper, 'duplicate manifest entry'))
    incomplete = dict(files)
    incomplete['SHA256SUMS'] = b'\n'.join(files['SHA256SUMS'].splitlines()[1:]) + b'\n'
    cases.append((incomplete, paper, 'manifest coverage'))
    cases.append((files, paper + b'\n# changed bytes\n', 'paper checker binding'))
    for packet, checker, expected in cases:
        try:
            validate(packet, checker)
        except SystemExit as error:
            need(str(error) == 'FAIL: ' + expected, 'integrity control failure')
        else:
            need(False, 'integrity control accepted')
    result_cases = [
        (1, b'valid\n', b'', 'child exit status'),
        (0, b'valid\n', b'unexpected\n', 'child standard error'),
        (0, b'wrong\n', b'', 'child standard output'),
    ]
    for status, stdout, stderr, expected in result_cases:
        try:
            validate_result(status, stdout, stderr, digest(b'valid\n'))
        except SystemExit as error:
            need(str(error) == 'FAIL: ' + expected, 'result control failure')
        else:
            need(False, 'result control accepted')
    return len(cases) + len(result_cases)


def main():
    need(len(sys.argv) == 1, 'runner takes no arguments')
    files, paper = inventory(), read_paper()
    validate(files, paper)
    control_count = integrity_controls(files, paper)
    flags = ['-O'] if sys.flags.optimize else []
    result = execute([sys.executable, '-P', '-S', '-s', '-B'] + flags +
                     [str(HERE / CHILD)], '1', 'exact supporting suites')
    validate_result(result.returncode, result.stdout, result.stderr, CHILD_STDOUT_SHA256)
    print(result.stdout.decode(), end='')
    previous = None
    paper_controls = 0
    for mode, flags, seed in MODES:
        command = [sys.executable, '-P', '-S', '-s', '-B'] + flags + [str(ROOT / PAPER)]
        result = execute(command, seed, 'paper examples: ' + mode)
        validate_result(result.returncode, result.stdout, result.stderr, PAPER_STDOUT_SHA256)
        need(previous is None or result.stdout == previous, 'paper mode output mismatch')
        previous = result.stdout
        for name, error in CONTROL_ERRORS.items():
            result = execute(command + ['--negative-control', name], seed,
                             'paper control: ' + name + ': ' + mode)
            need(result.returncode == 1 and not result.stdout and result.stderr == error,
                 'paper rejection: ' + name + ': ' + mode)
            paper_controls += 1
    need(inventory() == files and read_paper() == paper, 'files changed during execution')
    validate(inventory(), read_paper())
    print('PASS: paper examples in normal, optimized and hash-seed modes')
    print('PASS: ' + str(paper_controls) + ' reason-specific paper negative-control runs')
    print('PASS: ' + str(control_count) + ' entrypoint integrity controls rejected')
    print('RESULT: PASS two-vertex sign regularity verification')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, TypeError, KeyError, UnicodeError) as error:
        raise SystemExit('FAIL: verification input: ' + type(error).__name__)
