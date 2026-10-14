# Exact verification

Run `python3 -S -s -B run.py` from
this directory with Python 3.11 or later. Only the standard library is
needed. All arithmetic in the two checkers uses integers or `Fraction`.

`check_fekete_and_corners.py` checks 71,280 Fekete identities, 2,920
corner checks including four formal polynomial identities, 2,956 fixture
minors and two checker-vertex pairs. Its six negative controls reverse
an identity sign, alter a signature or entry, make an endpoint singular,
or reverse the claimed checker ordering.

`check_schur_and_rank.py` checks 1,632 fixture minors, 1,179 signed Schur
identities, four rank examples and two basis extensions. It also checks
an endpoint-zero example with midpoint value $1/4$, which rules out an
unjustified endpoint-only argument. Its five negative controls remove
insertion signs or give incorrect rank, signature or nonsingularity claims.

The universal conclusion rests on the [written proof](../proofs/PROOF.md).
The finite fixtures do not prove the all-dimension theorem.

## Bindings and execution

`CHECKERS.txt` records each checker's expected stdout SHA256.
`NEGATIVE_CONTROLS.json` records every negative-control name and its exact
expected stderr. Each control must exit with status 1 and empty stdout.
Normal checker executions must exit zero, produce no stderr and match
their registered output hashes.

The runner executes each checker and all its controls in three modes:
normal with hash seed 1, `-O` with seed 1, and normal with seed 8675309.
Site initialization and bytecode writes are disabled. The three positive
outputs must be byte-identical. In total, six positive executions and
33 negative-control executions must pass their respective checks.

`SHA256SUMS` covers every verification file except itself, including the
runner, this guide, registries and fixture. The runner checks complete
manifest and checker coverage, standard-library imports, absence of
assertions and inexact literals, and JSON with unique keys and integer
numbers. Symbolic links, bytecode files and unexpected files fail.
`SOURCE_BINDINGS.txt` records the source and included proof hashes; the
runner verifies the two included files under `proofs/`. All verification
and proof hashes are checked again after execution. A mismatch exits
nonzero, including under `-O`.
