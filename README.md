# Two-vertex certification of nonsingular sign-regular matrix intervals

Authors: TBD

Read the [paper](paper/main.pdf) and its [LaTeX source](paper/main.tex).
The theorem answers the [catalogue question](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/d49c11a1b2091547235e4779f7e067ed4b65774d/intervals-and-absolute-value-equations/IV-01/README.md)
affirmatively, including arbitrary fixed entries and vanishing proper minors.

## Main theorem

Let $n\geq1$, let $\epsilon\in\{-1,1\}^n$, and let
$L,U\in\mathbb R^{n\times n}$ satisfy $L\leq U$ entrywise.
A matrix $X$ is nonsingular sign regular with signature $\epsilon$ when
$\det X\ne0$ and

$$
\epsilon_k\det X[I,J]\geq0
\qquad (1\leq k\leq n,\quad |I|=|J|=k),
$$

for every pair of increasing row and column index sets. Define the two
checker vertices, using one-based indices, by

$$
A^-_{ij}=\begin{cases}L_{ij},&i+j\text{ even},\\U_{ij},&i+j\text{ odd},\end{cases}
\qquad
A^+_{ij}=\begin{cases}U_{ij},&i+j\text{ even},\\L_{ij},&i+j\text{ odd}.\end{cases}
$$

Then every real $X$ with $L\leq X\leq U$ is nonsingular sign regular
with signature $\epsilon$ **if and only if** both $A^-$ and $A^+$ have
that property with the same signature.

There is no restriction on which entries are fixed, on the parity of
fixed positions, or on zero proper minors. The entries need not be
rational. Endpoint nonsingularity and the common signature are required.
The catalogue asks for $n\geq5$; the theorem holds for every positive
dimension. The proof treats weak signs directly, without a strictness or
genericity assumption.

## Evidence status

- **Formally proved in Lean 4 with Mathlib:** `IV01.twoCheckerVertices`
  proves the complete implication from the two checker vertices to every
  real matrix in the box. Its hypotheses are exactly the box, signature,
  and endpoint hypotheses above, with $n\geq1$. The reverse implication
  follows from the proved membership of both checker vertices in the box.
  The transitive axiom report contains only `propext`, `Classical.choice`,
  and `Quot.sound`. See the [statement correspondence](LEAN_STATEMENT_CORRESPONDENCE.md)
  and [verification record](VERIFICATION.md).
- **Exact computation:** standard-library integer and rational checks
  verify determinant identities, rank examples, boundary fixtures, and
  all four examples in the paper. Corrupted inputs and incorrect claims
  must be rejected. Normal and optimized Python runs give identical output.
  These finite checks supplement the uniform proof.
- **Proved in the paper:** Theorem 1.1 has the complete formal counterpart
  above. Some stronger auxiliary formulations, the contextual discussion,
  and the certification-cost discussion are established in the paper;
  the [section map](paper-lean-mapping/by-section.md) gives their precise scope.
- **Scope:** the stated square, real, nonsingular interval question is
  settled. The theorem does not remove the endpoint nonsingularity or
  common-signature hypotheses, replace checker vertices by ordinary
  lower and upper bounds, or assert a rectangular analogue.

## Where to read

Start with the [guide from the question to the checks](paper-lean-mapping/README.md),
then the [paper](paper/main.pdf). The
[section-by-section map](paper-lean-mapping/by-section.md) identifies
formal statements and exact examples. The
[statement correspondence](LEAN_STATEMENT_CORRESPONDENCE.md) compares the
catalogue target item by item with the Lean definitions and theorem.

The [Lean guide](lean/README.md), [exact-check guide](verification/README.md),
and [verification record](VERIFICATION.md) give reproduction commands.

## Reproduce the checks

Use Python 3.11 or later:

```sh
python3 -S -s -B verification/run.py
python3 -S -s -B -O verification/run.py
python3 -B paper-lean-mapping/build_and_check.py
python3 -B -O paper-lean-mapping/build_and_check.py
python3 -I -B tools/check_markdown_math.py
```

With the pinned Lean toolchain installed through elan:

```sh
cd lean
lake exe cache get
python3 -B verify.py
```

The Lean guide describes the dependency pins and the fresh compilation.
The [paper guide](paper/README.md) gives the LaTeX build command.

## Layout

- `paper/`: manuscript source, bibliography, PDF, and exact example checker.
- `lean/`: complete pinned Lean project and verification evidence.
- `paper-lean-mapping/`: reading guide, result map, and reference checker.
- `verification/`: supporting written proof and exact checks with one entry point.
- `tools/`: a static guard for GitHub Markdown math.

## License and citation

Files outside `paper/` are available under the [MIT license](LICENSE).
The [paper license](paper/LICENSE) is TBD.
Author information is TBD in [CITATION.cff](CITATION.cff).

## Acknowledgements

TBD.
