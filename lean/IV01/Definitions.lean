import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/-!
# IV-01: the exact predicates

Indices in Lean start at zero. This does not change checker parity, since
shifting both the row and column index to one-based indexing adds two.
The signature is indexed by the order of a minor; values outside `1, …, n`
are irrelevant. All minors use strictly increasing row and column maps.
-/

namespace IV01

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def IsSignature (n : ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → ε k = 1 ∨ ε k = -1

noncomputable def minor {n k : ℕ} (M : Square n)
    (rows cols : Fin k → Fin n) : ℝ :=
  Matrix.det (M.submatrix rows cols)

def SignRegular {n : ℕ} (ε : ℕ → ℝ) (M : Square n) : Prop :=
  ∀ k, 1 ≤ k → k ≤ n → ∀ rows cols : Fin k → Fin n,
    StrictMono rows → StrictMono cols → 0 ≤ ε k * minor M rows cols

def NonsingularSignRegular {n : ℕ} (ε : ℕ → ℝ) (M : Square n) : Prop :=
  Matrix.det M ≠ 0 ∧ SignRegular ε M

def EntrywiseLE {n : ℕ} (L U : Square n) : Prop :=
  ∀ i j, L i j ≤ U i j

def InBox {n : ℕ} (L U M : Square n) : Prop :=
  EntrywiseLE L M ∧ EntrywiseLE M U

def checkerMinus {n : ℕ} (L U : Square n) : Square n :=
  fun i j => if (i.val + j.val) % 2 = 0 then L i j else U i j

def checkerPlus {n : ℕ} (L U : Square n) : Square n :=
  fun i j => if (i.val + j.val) % 2 = 0 then U i j else L i j

end IV01
