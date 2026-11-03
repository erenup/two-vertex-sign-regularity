# Paper v2: Two Vertices Certify a Whole Interval of Nonsingular Sign-Regular Matrices

Authors: Wenqi Zhu; Kai Zou; Ping Nie.

[main.pdf](main.pdf) is a revised exposition of Theorem 1.1 of the
[paper](../paper/main.pdf), organized as a six-step proof of the
Garloff–Adm–Titi interval conjecture. The theorem is unchanged. The Lean proof,
the paper-to-Lean map and the exact checks refer to [paper/](../paper/).

The source is [main.tex](main.tex), with bibliography [refs.bib](refs.bib).
Build from this directory with LaTeX, BibTeX and `latexmk`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

All files in this directory are licensed under [CC BY-SA 4.0](LICENSE).
