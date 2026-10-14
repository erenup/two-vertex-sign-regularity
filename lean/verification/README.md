# Dated Lean verification evidence

The build recorded here completed successfully on 2026-10-14, from
20:15:56Z to 20:19:26Z. It compiled all 41 production modules into initially
empty project objects and inspected the transitive axiom dependencies of
`IV01.twoCheckerVertices`.

| File | Contents |
| --- | --- |
| [2026-10-14-build.log](2026-10-14-build.log) | Dated build transcript and successful final checks |
| [2026-10-14-axioms.log](2026-10-14-axioms.log) | Literal output of `#print axioms IV01.twoCheckerVertices` |
| [2026-10-14-receipt.json](2026-10-14-receipt.json) | Module object hashes, source/configuration/helper hashes, and run times |
| [2026-10-14-dependencies.json](2026-10-14-dependencies.json) | Compiler identity, nine dependency revisions and artifact-hash summary |
| [2026-10-14-controls.json](2026-10-14-controls.json) | Twenty-five rejection and positive controls per Python execution mode |

The exact axiom output is:

```text
'IV01.twoCheckerVertices' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every production Lean source was fixed by the source inventory before and
after compilation. Dependency libraries came from the pinned local cache;
the compiler identity, all nine dependency revisions, tracked source
cleanliness and all library artifact bytes were checked before and after
the build. The full dependency snapshot hash is recorded in the dependency
summary. These checks identify the trusted compiler and dependency inputs;
they do not independently rebuild those inputs.

To reproduce the proof check on Linux x86_64, install the pinned Lean
release, put `lake` on `PATH`, and run from the `lean/` directory:

```sh
lake exe cache get
python3 -B audit/test_verify.py
python3 -O -B audit/test_verify.py
python3 -B test_verify.py
python3 -O -B test_verify.py
python3 -B verify.py --output .audit-build
```

The output directory must not already exist. The last command creates fresh
project objects, the complete dependency artifact snapshot, a build receipt,
and per-module compiler logs. It finishes by running the fixed
`audit/Axioms.lean` probe with only those fresh project objects and the
pinned dependency libraries available for imports. A successful run permits
only the three displayed standard axioms.
