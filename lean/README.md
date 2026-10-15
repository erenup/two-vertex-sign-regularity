# Lean proof of the two-checker-vertex theorem

[`IV01.twoCheckerVertices`](IV01/Statement.lean) proves the theorem in every
positive dimension. Let $L$ and $U$ be arbitrary real square matrices with
$L\le U$ entrywise, and let $`\varepsilon_k\in\{-1,1\}`$ for every minor order.
If both checker vertices have nonzero determinant and all increasing-index
minors satisfy $`\varepsilon_k\det M[I,J]\ge0`$, then every matrix in the
entrywise interval has those same properties. Proper minors may vanish.

The [definitions](IV01/Definitions.lean) use `Matrix (Fin n) (Fin n) ℝ`,
strictly increasing row and column maps, and the two entrywise alternating
choices of $L$ and $U$. No additional geometric, algebraic, or computational
premise is imposed. The [statement correspondence](../LEAN_STATEMENT_CORRESPONDENCE.md)
identifies the catalogue quantifiers and each formal hypothesis. The
[paper mapping](../paper-lean-mapping/README.md) connects the written proof
to the formal declarations.

## Build and verify

The project pins Lean `v4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, and Mathlib revision
`85e3a25e006c35636f0e53b0e9296caca2685bc0`. All nine dependency revisions
are fixed in [`lake-manifest.json`](lake-manifest.json).
Install Lean through [elan](https://github.com/leanprover/elan), make `lake`
available on `PATH`, and use Python 3.11 or later. From this directory:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -O -B audit/test_verify.py
python3 -B test_verify.py
python3 -O -B test_verify.py
python3 -B verify.py
```

The first command downloads the official dependency cache. From the repository
root, the final command is `python3 -B lean/verify.py`. The standalone verifier
supports Linux x86_64 and pins the compiler binary SHA256. It creates a new
`.audit-build/` directory and refuses to overwrite an existing output; pass
`--output /path/to/new-directory` for another build. It compiles all 41
production modules with one compiler thread and a 12 GiB compiler limit.
Allow up to 16 GiB of memory.

Only freshly compiled project objects and the pinned dependency libraries
are on the import path. The verifier checks all dependency Git revisions and
tracked source cleanliness, and hashes the installed toolchain libraries and
dependency library artifacts before and after compilation. It checks the
complete Lean source inventory, the fixed source digests, the build
configuration, and the verification helper bytes for changes.

The final probe is the literal `#print axioms IV01.twoCheckerVertices` in
[`audit/Axioms.lean`](audit/Axioms.lean). This command reports the transitive
axiom dependencies of the target. The verifier requires exactly `propext`,
`Classical.choice`, and `Quot.sound`; any additional or missing output fails.
The source checks reject proof placeholders, local axiom declarations and
native-execution proof shortcuts. Failed compilation or malformed output
also fails the verification.

The installed compiler and official dependency cache are trusted inputs.
The binary, revision, source-cleanliness and library-byte checks establish
their exact identities and stability for the run; they do not reconstruct
the original build of those dependency objects. No existing local theorem
object is used as proof input.

The [dated evidence](verification/README.md) contains a successful build log,
the transitive axiom output, dependency summary and build receipt. A new
run writes the full dependency artifact hashes, per-module compiler output
and object hashes into its output directory.

For a conventional Lake build and direct axiom inspection, run:

```sh
lake build
lake env lean audit/Axioms.lean
```

The source and output controls pass both normal and optimized Python
execution. They reject missing or changed source files, extra unbound Lean
modules, redirected build configuration, forged axiom output, duplicate or
unexpected axiom names, linked project inputs and failed child processes.
