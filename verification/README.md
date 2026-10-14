# Exact supporting checks

Run from the repository root with Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Only the Python standard library is required. The commands must exit
zero, have empty standard error, and produce identical standard output.
The entry point authenticates its complete file inventory, nested runner
and manifest, and the paper example checker before running them.

The [determinant and rank suite](core/verification/README.md) checks
Fekete identities, rank-one corners, signed Schur identities, rank
examples, basis extensions, and boundary fixtures. Its mathematical
programs use integers and `Fraction`. It executes two checkers in three
modes and rejects eleven distinct mathematical controls in every mode,
for 33 rejection runs. The original written
[statement](core/proofs/STATEMENT.md) records the catalogue range of
dimensions; its [proof](core/proofs/PROOF.md) is supplemented by the
all-positive-dimension paper and Lean theorem.

The [paper checker](../paper/check_examples.py) verifies four examples:
singular endpoints, differing endpoint signatures, ordinary lower and
upper bounds, and a five-dimensional box with zero proper minors and
fixed entries of both parities. It checks all sixteen ordinary vertices
of the last example. Four reason-specific controls are rejected in each
of three modes, for twelve further rejection runs.

The entry point also exercises eleven inventory and process-result
rejection controls. Changed files, incomplete or duplicated manifests,
missing or extra files, altered checker bindings, unexpected output,
standard error, or a failed child process cause failure. Its recursive
inventory rejects symlinks. Checks remain active under `-O`.

The supporting proof and nested checker manifests are authenticated.
The universal theorem is proved by the Lean target
`IV01.twoCheckerVertices`; these finite calculations do not establish
it on their own. See [VERIFICATION.md](../VERIFICATION.md) for outputs
and the formal verification record.
