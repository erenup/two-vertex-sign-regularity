# Two-vertex certification of nonsingular sign-regular matrix intervals

Authors: TBD

The [paper](main.pdf) proves Theorem 1.1 for every positive integer
dimension and every signature. A real square entrywise matrix box
consists of nonsingular sign-regular matrices if and only if its two
checker vertices do, with the same signature. Zero proper minors and
arbitrary fixed entries are allowed.

The source is [main.tex](main.tex), with bibliography [refs.bib](refs.bib).
Build from this directory with LaTeX, BibTeX, and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=build/ci main.tex
```

The rebuilt PDF is `build/ci/main.pdf`. The included `main.pdf` has the
same mathematical content. Standard TeX Live packages, including `lmodern`
and TikZ, suffice. The author placeholder in the source and PDF is
`[Authors to be decided]`.

[check_examples.py](check_examples.py) checks all four examples with
standard-library rational arithmetic. From the repository root, the
[single entry point](../verification/run.py) runs this checker in normal,
optimized, and alternate hash-seed modes, checks the expected output,
and requires all four mathematical negative controls to fail in each mode.

The five-dimensional example is checked at both checker vertices and
all sixteen ordinary vertices. The finite examples illustrate the theorem;
the uniform theorem has a [complete Lean proof](../lean/IV01/Statement.lean).

The manuscript [license](LICENSE) is TBD.
