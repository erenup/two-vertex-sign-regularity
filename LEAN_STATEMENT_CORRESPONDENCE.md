# Lean statement correspondence

The target is the catalogue IV-01 problem at immutable revision
`d49c11a1b2091547235e4779f7e067ed4b65774d`,
[canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/d49c11a1b2091547235e4779f7e067ed4b65774d/intervals-and-absolute-value-equations/IV-01/README.md).
The full canonical README at that revision has SHA256
`420f9e3cfc8d558b3b9fbb30385e866ed1c3d15cecb3dcd6b19e1cb50e8eda45`.
The problem statement and question below are reproduced verbatim from
that snapshot, through the paragraph before its References section.

## Problem statement

For $`\epsilon\in\{-1,1\}^n`$, call a real $`n\times n`$ matrix $`M`$
**nonsingular sign regular with signature** $`\epsilon`$ if $`\det M\ne0`$ and
every minor of order $`k`$ has determinant $`d`$ satisfying $`\epsilon_k d\ge0`$,
for every $`1\le k\le n`$.

Let $`n\ge5`$ and let $`L,U\in\mathbb R^{n\times n}`$ satisfy $`L\le U`$
entrywise. Define the two checkerboard vertex matrices

```math
A^-_{ij}=\begin{cases}L_{ij},&i+j\text{ even},\\U_{ij},&i+j\text{ odd},\end{cases}
\qquad
A^+_{ij}=\begin{cases}U_{ij},&i+j\text{ even},\\L_{ij},&i+j\text{ odd}.\end{cases}
```

### Question

If $`A^-`$ and $`A^+`$ are nonsingular sign regular with the same
signature $`\epsilon`$, must every real matrix $`M`$ with $`L\le M\le U`$ be
nonsingular sign regular with signature $`\epsilon`$?

The implication would certify a property of an entire interval of matrices
from only two of its vertices. Allowing zero minors is essential to the
remaining problem.

## Target declaration

The declaration is
[`IV01.twoCheckerVertices`](lean/IV01/Statement.lean).
It has the following full signature:

```lean
theorem twoCheckerVertices
    (n : ℕ) (hn : 1 ≤ n) (ε : ℕ → ℝ) (hε : IsSignature n ε)
    (L U : Square n) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (M : Square n) (hM : InBox L U M) :
    NonsingularSignRegular ε M
```

There is no additional typeclass, oracle, genericity condition, rank
hypothesis, unproved lemma, or externally supplied proof premise in
this target signature. Its proof supplies the fixed, positive-sign,
and negative-sign rectangle exclusions by proved Lean declarations.
Those exclusions are dependencies, not assumptions imposed on the user.

## Definitions, quantifiers, and premises

All predicates in the target are defined in
[`IV01/Definitions.lean`](lean/IV01/Definitions.lean).

| Catalogue item | Lean expression | Exact correspondence |
|---|---|---|
| Every integer dimension $n\geq5$ | `n : ℕ`, `hn : 1 ≤ n` | The formal theorem is stronger in dimension: it covers every positive natural number. The catalogue range implies this premise. Dimension zero is outside both targets. |
| Every real square matrix | `Square n := Matrix (Fin n) (Fin n) ℝ` | Entries range over all real numbers, with no rationality, boundedness, or strict-positivity condition. |
| Signature $`\epsilon\in\{-1,1\}^n`$ | `ε : ℕ → ℝ`, `IsSignature n ε` | For every `k` with `1 ≤ k ≤ n`, `ε k = 1 ∨ ε k = -1`. This encodes the finite tuple by its order index. Values at zero and beyond `n` are unrestricted and do not occur in the target predicates. Any catalogue tuple extends to such a function. |
| $L\leq U$ entrywise | `hLU : EntrywiseLE L U` | `∀ i j, L i j ≤ U i j`. Equal entries are allowed independently at every position. |
| Checker vertices $A^-,A^+$ | `checkerMinus L U`, `checkerPlus L U` | Each definition chooses exactly the displayed lower or upper entry according to `(i.val + j.val) % 2 = 0`. Lean uses zero-based indices. Shifting both indices to one-based indexing adds two, preserving parity and the vertex names. |
| Each minor of order $k$ | `minor M rows cols` | `Matrix.det (M.submatrix rows cols)`, with `rows cols : Fin k → Fin n`. Both maps are required to be `StrictMono`, so row and column order matches increasing index sets. Every increasing index set has its unique increasing enumeration, and every such map enumerates an index set. No minors are omitted. |
| Weak sign regularity | `SignRegular ε M` | For every `k`, `1 ≤ k`, `k ≤ n`, and every pair of strictly increasing row and column maps, `0 ≤ ε k * minor M rows cols`. The inequality is weak; zero proper minors are permitted. |
| Endpoint nonsingularity and a common signature | `hminus`, `hplus` | `NonsingularSignRegular ε X` is exactly `Matrix.det X ≠ 0 ∧ SignRegular ε X`. Both endpoint assumptions use the same `ε`. These are the catalogue assumptions. |
| Every real matrix $M$ with $L\leq M\leq U$ | `M : Square n`, `hM : InBox L U M` | `InBox` is `EntrywiseLE L M ∧ EntrywiseLE M U`. All endpoints, boundary faces, and interior points are included. |
| Required conclusion | `NonsingularSignRegular ε M` | The conclusion states both `det M ≠ 0` and the prescribed weak sign of every minor, for the original common signature. |

Every target premise is either the corresponding catalogue assumption
or the weaker positive-dimension premise implied by its dimension range.
In particular, nonsingularity is assumed only for the two checker
vertices and is proved for every matrix in the interval.

## Relation to Theorem 1.1 of the paper

The paper states an equivalence for every $n\geq1$. The target above
proves the nontrivial direction and thus answers the catalogue question
in full. The converse is immediate by specializing the universal box
property to each checker vertex. Their membership is proved in
[`IV01/Box.lean`](lean/IV01/Box.lean) as
`IV01.checkerMinus_mem_box` and `IV01.checkerPlus_mem_box`.
There is no separately named bundled equivalence declaration.

The [supporting statement](verification/core/proofs/STATEMENT.md) uses
the narrower catalogue range $n\geq5$; the paper and formal target both
use $n\geq1$. This range difference strengthens the result and does not
leave any catalogue case unresolved. Internal auxiliary results do not
all have the same grouping or strength as the paper's lemmas. The
[section map](paper-lean-mapping/by-section.md) states those differences;
they do not add any premise to the target declaration.

## Verification evidence

The [verification record](VERIFICATION.md) gives the pinned compiler and
dependencies, commands, dated successful log, and transitive axiom output.
The axiom closure of the target is restricted to `propext`,
`Classical.choice`, and `Quot.sound`; the recorded checker rejects every
other axiom and additional native execution trust.

The catalogue's [Lean evidence requirements](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/CONTRIBUTING.md#lean-verification)
and [status definitions](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/README.md#problem-status)
were consulted on 2026-10-14. The files here provide the statement
comparison and reproducible formal evidence. They make no assertion
that the catalogue has rerun these commands or changed its status.
