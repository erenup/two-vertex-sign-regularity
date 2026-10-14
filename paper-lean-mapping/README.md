# From two vertices to every matrix in the box

Let L and U be real square matrices with L <= U entrywise. At positions
with even row-plus-column index, choose L for the minus checker vertex
and U for the plus checker vertex; at odd positions, reverse the choices.
These two vertices certify the entire interval: for every positive
dimension and every fixed signature, the box consists of nonsingular
weakly sign-regular matrices exactly when both checker vertices have
that property. Zero proper minors and fixed entries of both parities
are allowed.

The [paper](../paper/main.pdf) proves this theorem by induction on minor
order. The [Lean project](../lean/README.md) proves the complete
checker-vertex-to-box implication in
[`IV01.twoCheckerVertices`](../lean/IV01/Statement.lean). Its assumptions
are precisely the positive dimension, a signature whose entries are
either -1 or 1, entrywise ordered real bounds, the two nonsingular
sign-regular checker vertices, and membership of the matrix in the box.
Its conclusion includes every weak minor sign and nonsingularity.
The reverse implication follows from the two separately proved
checker-vertex membership facts.

Lean uses zero-based matrix indices. Shifting both indices to the
one-based paper convention adds two to their sum and preserves checker
parity. Signatures are indexed by minor order. Their values outside
orders 1 through n are irrelevant; the empty pivot has sign 1 without
imposing a value on the signature at zero. Increasing row and column
maps specify the minor order. See
[LEAN_STATEMENT_CORRESPONDENCE.md](../LEAN_STATEMENT_CORRESPONDENCE.md)
for the item-by-item comparison with the catalogue statement.

## Follow the argument

The [section map](by-section.md) contains all 19 numbered results in the
paper: 15 theorem, proposition, corollary and lemma statements, and four
examples. Three additional entries identify the induction cases in
Section 7. The source labels, declaration names, exact-computation paths
and precise scopes are also recorded in [mapping.json](mapping.json).

Section 3 establishes nonsingularity and the first two minor signs. The
low-order corner statements in Section 4 support signed Schur elimination
in Section 5. Section 6 turns a hypothetical wrong-sign minor of minimal
span into a permanently deficient interior rectangle. A free entry in
that rectangle forces an essential row or column. The three proved
exclusion contracts then eliminate a fixed rectangle and both possible
normalized third-order signs for a free rectangle. The main declaration
supplies these proved contracts to the induction; it does not assume them.

The complete main theorem has a formal proof, while two stronger
intermediate statements in the paper have narrower isolated formal
counterparts:

- Lemma 3.1 concludes both nonsingularity and nonnegative inverse
  throughout an interval. The cited Lean declaration for that lemma
  proves nonsingularity. Its finite positive-supersolution proof is
  sufficient for the complete main theorem.
- Lemma 5.2 bounds `(row_count-p)(column_count-t)` by two, where t is
  the actual rectangle rank and t <= p. Its isolated Lean declaration
  bounds `(row_count-p)(column_count-p)` by two. This bound excludes
  both rectangle sizes used in the main proof, including when t < p.

The map also distinguishes the explicit zero-propagation declarations
from the paper's combined support-interval description, and records the
cofactor signs of Corollary 3.2 as consequences of the complete target.
These distinctions describe the cited intermediate declarations; they do
not restrict the hypotheses or conclusion of the main theorem.

## Exact examples

The four examples in Section 8 illustrate why nonsingularity, a common
signature and the checker choice matter, and exhibit a degenerate box
with four independent parameters. The rational program
[`paper/check_examples.py`](../paper/check_examples.py) computes all
relevant minors. It checks all 16 ordinary vertices of the final
five-dimensional box. Multiaffine interpolation connects those finite
vertex calculations to that particular box.

The first and third examples have direct-sum extensions to arbitrary
dimension in the written proof. The program checks the first at orders
3 and 5, and the third at orders 2 and 5. It does not replace their
all-dimensional arguments. The second example stays in dimension two.
No Lean declaration specializes the theorem to these rational matrices.
The [verification entry point](../verification/run.py) includes the
exact computations and their rejection controls; commands and separate
Lean verification are in [VERIFICATION.md](../VERIFICATION.md).

## Check the map

Run from the repository root with Python 3.11 or later:

```sh
python3 -B paper-lean-mapping/build_and_check.py
python3 -O -B paper-lean-mapping/build_and_check.py
```

The checker uses only the standard library, leaves the files unchanged,
and produces identical output in both modes. It reads the paper's
section and shared theorem counters, requires every numbered result,
checks every label and cited Lean theorem or lemma in its namespace,
and requires the generated section table to match exactly. Comments and
strings do not count as Lean declarations. Missing files, malformed map
data, duplicate records and unsupported counter changes cause failure.
Its corruption controls remain active with Python `-O`.

Both commands print:

```text
PASS: 19 numbered paper results, 3 induction cases; labels, declarations, exact-check paths and section table; 22 rejection controls
```

This is a reference and inventory check. It does not compile Lean,
execute the mathematical checks or validate the PDF. The separate Lean
build and transitive axiom report establish the formal evidence described
in [VERIFICATION.md](../VERIFICATION.md).

After an intentional change to the map, regenerate the section table:

```sh
python3 -B paper-lean-mapping/build_and_check.py --write
```

The map is validated before `by-section.md` is written.
