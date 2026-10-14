# IV-01: two checker vertices certify nonsingular sign regularity

## Exact theorem

For every integer n>=5, every signature
epsilon=(epsilon_1,...,epsilon_n) in {-1,+1}^n, and every pair of real
n-by-n matrices L<=U entrywise, define

    A^-_ij = L_ij if i+j is even, and U_ij if i+j is odd;
    A^+_ij = U_ij if i+j is even, and L_ij if i+j is odd.

Indices start at 1. Suppose both endpoint determinants are nonzero and,
for every k=1,...,n, every k-minor D of either endpoint satisfies
epsilon_k D>=0. Then **every real matrix M with L<=M<=U is nonsingular
and every one of its k-minors satisfies epsilon_k D>=0, for every k**.

Thus the answer to the catalogue question is **yes**. The converse is
immediate because the two vertices belong to the interval.

Zero entries and zero minors of every proper order are allowed. Fixed
entries can have either or both checker parities. There is no genericity,
strict-minor, rational-entry, or dimension bound beyond the displayed
n>=5. No numerical approximation is part of the proof.

## Proof package

`PROOF.md` is a self-contained written proof. It reduces a smallest
wrong-sign minor to a rank-deficient interior rectangle. Independent
entry variations can occur only on essential rows or columns. Signed
Schur complements and the support of nonnegative sign-regular matrices
exclude those variations; a fixed rectangle is excluded by shared
rank-one corners and an affine midpoint argument.

## Target and sources

Catalogue target:
https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/intervals-and-absolute-value-equations/IV-01/README.md

The catalogue cites Garloff--Adm--Titi, *A Survey of Classes of Matrices
Possessing the Interval Property and Related Properties*, Reliable
Computing 22 (2016), and Adm--Garloff, *Certification of the Sign
Regularity of Matrix Intervals*, Acta Scientiarum Mathematicarum (2026),
DOI https://doi.org/10.1007/s44146-026-00223-y.

The supplied Holden IV-01 manuscripts motivated the entry/order-two and
inverse-positive reductions; these reductions are re-proved in the
package. The higher-order proof does not assume the earlier sufficient
conditions or any unresolved statement.
