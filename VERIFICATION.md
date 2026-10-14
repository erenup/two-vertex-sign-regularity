# Verification

All recorded commands completed on 2026-10-14. Python checks use only the
standard library; the mathematical programs use exact integer or rational
arithmetic. The full real-matrix theorem is proved by the Lean declaration
`IV01.twoCheckerVertices`. The finite programs provide supporting checks
and examples.

## Exact arithmetic and negative controls

From the repository root with Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
```

Both commands exit zero with empty standard error and identical standard
output:

```text
PASS: check_fekete_and_corners.py (normal, optimized, hash-seed)
PASS: check_schur_and_rank.py (normal, optimized, hash-seed)
PASS: 33 negative-control runs; 2 proof bindings
RESULT: PASS IV-01 verification
PASS: paper examples in normal, optimized and hash-seed modes
PASS: 12 reason-specific paper negative-control runs
PASS: 11 entrypoint integrity controls rejected
RESULT: PASS two-vertex sign regularity verification
```

The standard-output SHA256 is
`bc85e7dc24b74bf65ad9411883ad03b7c76a0a1363d1916f57b562c66b4d2dff`.

Each command performs 45 reason-specific mathematical rejection runs:
eleven determinant/rank controls in three modes, and four paper-example
controls in three modes. The modes are ordinary Python with hash seed 1,
optimized Python with seed 1, and ordinary Python with seed 8675309.
Eleven further in-memory inventory and child-result controls reject
changed code, incomplete or duplicated manifests, missing or extra files,
changed bindings, unsuccessful processes, standard error, and unexpected
output. The runner also rejects symlinks and changes during execution.
The root entry point authenticates the nested runner, nested manifest,
and paper checker. The nested suite authenticates the two supporting
proof documents. See the [exact-check guide](verification/README.md).

## Complete Lean theorem

The project pins Lean `v4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. All nine dependency
revisions are pinned in [lake-manifest.json](lean/lake-manifest.json).

Install the pinned release through elan, then run from `lean/`:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -O -B audit/test_verify.py
python3 -B test_verify.py
python3 -O -B test_verify.py
python3 -B verify.py --output .audit-build
```

The final output directory must be new. See the [Lean guide](lean/README.md)
for the Linux x86_64 compiler pin and resource requirements. The formal
check completed from **2026-10-14T20:15:56Z to 2026-10-14T20:19:26Z**.
It compiled all **41 production modules** into initially empty project
objects, then ran the fixed `#print axioms IV01.twoCheckerVertices` probe.
The literal transitive axiom output is:

```text
'IV01.twoCheckerVertices' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The verifier permits only this exact standard-axiom set. It rejects proof
placeholders, local axiom declarations and native-execution proof shortcuts.
The target's complete [statement correspondence](LEAN_STATEMENT_CORRESPONDENCE.md)
identifies every hypothesis and its relationship to the catalogue target.
The formal theorem is for all positive dimensions, so it includes the
catalogue's range of dimensions at least five.

The [dated build transcript](lean/verification/2026-10-14-build.log),
[axiom output](lean/verification/2026-10-14-axioms.log),
[build receipt](lean/verification/2026-10-14-receipt.json),
[dependency summary](lean/verification/2026-10-14-dependencies.json), and
[control record](lean/verification/2026-10-14-controls.json) bind the successful
run to its source, configuration, compiler, and dependency inputs.

Only the fresh project objects and pinned dependency libraries were on
the import path. All nine dependency Git revisions and tracked source
cleanliness were checked; compiler, toolchain libraries, dependency
libraries, project sources, configuration and helpers remained unchanged.
The installed compiler and pinned local dependency cache are trusted
inputs; their original builds were not independently reconstructed.
The log makes no claim that the catalogue ran these commands.

The two control suites pass 17 and 8 tests, respectively, in each Python
mode. Their statuses and diagnostic text match after removing the
unittest elapsed-time field. They cover source inventory and digests,
configuration redirection, forged or extra axiom output, failed commands,
missing imports and import cycles, compiler identity, fresh-output guards,
dependency symlink escape, and theorem-object shadowing.

## Paper-to-Lean correspondence map

From the repository root:

```sh
python3 -B paper-lean-mapping/build_and_check.py
python3 -B -O paper-lean-mapping/build_and_check.py
```

Both commands exit zero with empty standard error and identical output:

```text
PASS: 19 numbered paper results, 3 induction cases; labels, declarations, exact-check paths and section table; 22 rejection controls
```

The standard-output SHA256 is
`0d9b290dee6afdf4b59ab4a3d352600b1fed273bec6a01f7ce59d8f11b607554`.
The complete numbered-result inventory contains 15 mathematical results
and four examples. Three additional records describe the induction cases.
The checker verifies labels, actual Lean declarations after removing
comments and strings, program paths, and the generated section table.
It runs 22 corruption controls in each mode. This checks references and
scope records; it does not infer mathematical equivalence from prose or
replace the Lean build.

The map explicitly distinguishes two stronger auxiliary paper claims:
inverse nonnegativity in Lemma 3.1 and the actual-rank-dependent bound
in Lemma 5.2. Their cited isolated Lean declarations prove the weaker
conclusions needed by the complete main proof. No extra premise remains
in `IV01.twoCheckerVertices`.

## Manuscript and Markdown

From `paper/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build/ci main.tex
```

This built 19 pages with no unresolved references or citations and no
overfull boxes. The included `paper/main.pdf` has SHA256
`5613667abfdcc82c047eb51c7744538ade60c0bc8a4b9bdf6e12b255acd6ad7d`.
The complete extracted text of the included and rebuilt PDFs is identical;
its SHA256 under `pdftotext -layout` is
`88c7be6b4dbf073535ed79ddd7829f262ae7106a2c747e126994bad8b0387ca2`.
PDF container metadata may differ between builds.

From the repository root:

```sh
python3 -I -B tools/check_markdown_math.py
python3 -I -B -O tools/check_markdown_math.py
```

The static guard checks all tracked Markdown files against the documented
GitHub math profile and exercises positive and negative controls. It does
not replace a live rendering check.

## File integrity

The root manifest lists every tracked file except itself. Run:

```sh
sha256sum --check SHA256SUMS
```

Nested manifests bind the exact suites and paper files. Dependency caches
and regenerated build products are excluded. File hashes establish byte
identity; the formal build and exact-check commands supply the associated
verification evidence.
