import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Cofactor relations for arbitrary rectangular matrices

These identities hold over any commutative ring and require no rank hypothesis.
They provide the algebraic cofactor relation used in Section 5.2 of the IV-01 proof.
-/

namespace IV01

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Each row annihilates the signed vector of maximal minors of a `k × (k+1)`
matrix. This is expansion of a determinant with a repeated row. -/
theorem cofactor_kernel_entry {k : ℕ}
    (A : Matrix (Fin k) (Fin (k + 1)) R) (i : Fin k) :
    ∑ j : Fin (k + 1),
      (-1 : R) ^ (j : ℕ) * A i j * (A.submatrix id j.succAbove).det = 0 := by
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
    Matrix.of (Matrix.vecCons (A i) A)
  have hz : B.det = 0 :=
    Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm (by rfl)
  rw [Matrix.det_succ_row_zero] at hz
  have hsub (j : Fin (k + 1)) :
      B.submatrix Fin.succ j.succAbove = A.submatrix id j.succAbove := by
    ext a b
    rfl
  simp only [hsub] at hz
  exact hz

/-- The signed maximal minors give a linear relation between the columns. -/
theorem cofactor_kernel {k : ℕ}
    (A : Matrix (Fin k) (Fin (k + 1)) R) :
    ∑ j : Fin (k + 1),
      ((-1 : R) ^ (j : ℕ) * (A.submatrix id j.succAbove).det) • A.col j = 0 := by
  ext i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    Pi.zero_apply, mul_assoc, mul_left_comm, mul_comm]
    using cofactor_kernel_entry A i

/-- Applying any linear functional to the cofactor relation. -/
theorem cofactor_kernel_linear {k : ℕ}
    (A : Matrix (Fin k) (Fin (k + 1)) R)
    (f : (Fin k → R) →ₗ[R] R) :
    ∑ j : Fin (k + 1),
      ((-1 : R) ^ (j : ℕ) * (A.submatrix id j.succAbove).det) * f (A.col j) = 0 := by
  simpa only [map_sum, map_smul, smul_eq_mul, map_zero]
    using congrArg f (cofactor_kernel A)

end IV01
