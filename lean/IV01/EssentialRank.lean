import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic

/-!
# Essential rows and columns under a one-entry perturbation

All index types are arbitrary finite types. The algebraic result only needs one
nonzero perturbation of rank at most the original rank; it therefore applies to
the two-sided local perturbations in Section 5.4 of the IV-01 proof.
-/

namespace IV01

open Matrix Module

variable {R m n : Type*} [Field R] [Fintype m] [Fintype n]

/-- The column space, used to make the rank arguments explicit. -/
def columnSpace (A : Matrix m n R) : Submodule R (m → R) :=
  Submodule.span R (Set.range A.col)

omit [Fintype m] in
theorem rank_eq_finrank_columnSpace (A : Matrix m n R) :
    A.rank = finrank R (columnSpace A) := A.rank_eq_finrank_span_cols

omit [Fintype m] [Fintype n] in
theorem col_mem_columnSpace (A : Matrix m n R) (j : n) :
    A.col j ∈ columnSpace A := Submodule.subset_span ⟨j, rfl⟩

omit [Fintype m] [Fintype n] in
/-- Restoring a deleted column restores at most one generator of the column space. -/
theorem columnSpace_deleteColumn_sup [DecidableEq n] (A : Matrix m n R) (j : n) :
    columnSpace A =
      columnSpace (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)) ⊔
        Submodule.span R {A.col j} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    by_cases hc : c = j
    · subst c
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · apply Submodule.mem_sup_left
      exact col_mem_columnSpace
        (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)) ⟨c, hc⟩
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro v ⟨c, rfl⟩
      exact col_mem_columnSpace A c.val
    · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (col_mem_columnSpace A j))

/-- A strict rank drop under one-column deletion is exactly a drop by one. -/
theorem rank_deleteColumn_add_one_of_lt [DecidableEq n] (A : Matrix m n R) (j : n)
    (h : (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank < A.rank) :
    (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank + 1 = A.rank := by
  let C := A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)
  have hj : A.col j ∉ columnSpace C := by
    intro hj
    have heq : columnSpace A = columnSpace C := by
      rw [columnSpace_deleteColumn_sup A j]
      exact sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hj))
    have hr : A.rank = C.rank := by
      rw [rank_eq_finrank_columnSpace, rank_eq_finrank_columnSpace, heq]
    exact (Nat.ne_of_lt h) hr.symm
  rw [rank_eq_finrank_columnSpace A, columnSpace_deleteColumn_sup A j,
    Submodule.finrank_sup_span_singleton hj]
  exact congrArg (· + 1) (rank_eq_finrank_columnSpace C)

/-- A strict rank drop under one-row deletion is exactly a drop by one. -/
theorem rank_deleteRow_add_one_of_lt [DecidableEq m] (A : Matrix m n R) (i : m)
    (h : (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank < A.rank) :
    (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank + 1 = A.rank := by
  have heq : (Aᵀ.submatrix id (Subtype.val : {a : m // a ≠ i} → m)).rank =
      (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank := by
    rw [← Matrix.transpose_submatrix, Matrix.rank_transpose]
  have h' : (Aᵀ.submatrix id (Subtype.val : {a : m // a ≠ i} → m)).rank < Aᵀ.rank := by
    simpa only [heq, Matrix.rank_transpose] using h
  simpa only [heq, Matrix.rank_transpose] using rank_deleteColumn_add_one_of_lt Aᵀ i h'

/-- If a coordinate vector belongs to the column space, removing the corresponding
row strictly reduces the rank. -/
theorem rank_deleteRow_lt_of_single_mem_columnSpace [DecidableEq m]
    (A : Matrix m n R) (i : m)
    (hi : Pi.single i (1 : R) ∈ columnSpace A) :
    (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank < A.rank := by
  let P := columnSpace A
  let π : (m → R) →ₗ[R] ({a : m // a ≠ i} → R) :=
    LinearMap.funLeft R R Subtype.val
  let f : P →ₗ[R] ({a : m // a ≠ i} → R) := π.comp P.subtype
  have hrange : LinearMap.range f =
      columnSpace (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    simp only [P, columnSpace, Submodule.map_span, ← Set.range_comp]
    rfl
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro hk
    have hv : (⟨Pi.single i (1 : R), hi⟩ : P) ∈ LinearMap.ker f := by
      change π (Pi.single i (1 : R)) = 0
      ext a
      simp [π, LinearMap.funLeft_apply, a.property]
    rw [hk, Submodule.mem_bot] at hv
    have he := congrArg (fun v : P => (v : m → R) i) hv
    simp at he
  have hpos : 0 < finrank R (LinearMap.ker f) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hdim := f.finrank_range_add_finrank_ker
  rw [hrange] at hdim
  rw [rank_eq_finrank_columnSpace, rank_eq_finrank_columnSpace]
  change finrank R (columnSpace _) < finrank R P
  omega

/-- A nonzero rank-preserving change in one column along a coordinate vector
forces its row or column to be essential. -/
theorem essential_row_or_column_of_column_perturbation [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n R) (i : m) (j : n) (t : R) (ht : t ≠ 0)
    (hrank : B.rank ≤ A.rank)
    (hother : ∀ c, c ≠ j → B.col c = A.col c)
    (hchange : B.col j = A.col j + t • Pi.single i (1 : R)) :
    (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank < A.rank ∨
      (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank < A.rank := by
  classical
  by_cases hc :
      (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank < A.rank
  · exact Or.inr hc
  left
  let C := A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)
  have hCA : columnSpace C ≤ columnSpace A := by
    apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    exact col_mem_columnSpace A c.val
  have hCB : columnSpace C ≤ columnSpace B := by
    apply Submodule.span_le.mpr
    rintro v ⟨c, rfl⟩
    change A.col c.val ∈ columnSpace B
    rw [← hother c.val c.property]
    exact col_mem_columnSpace B c.val
  have hCrank : C.rank = A.rank := by
    apply le_antisymm (A.rank_submatrix_le id Subtype.val)
    exact Nat.le_of_not_gt hc
  have hspace : columnSpace C = columnSpace A := by
    apply Submodule.eq_of_le_of_finrank_eq hCA
    simpa only [← rank_eq_finrank_columnSpace] using hCrank
  have hAB : columnSpace A ≤ columnSpace B := by
    rwa [hspace] at hCB
  have heq : columnSpace A = columnSpace B := by
    apply Submodule.eq_of_le_of_finrank_le hAB
    simpa only [← rank_eq_finrank_columnSpace] using hrank
  have hAj : A.col j ∈ columnSpace A := col_mem_columnSpace A j
  have hBj : B.col j ∈ columnSpace A := by
    rw [heq]
    exact col_mem_columnSpace B j
  have hsingle : t • Pi.single i (1 : R) ∈ columnSpace A := by
    have hs := (columnSpace A).sub_mem hBj hAj
    simpa [hchange] using hs
  apply rank_deleteRow_lt_of_single_mem_columnSpace A i
  have hs := (columnSpace A).smul_mem t⁻¹ hsingle
  simpa [smul_smul, ht] using hs

/-- Section 5.4 in its exact rank form: a nonzero one-entry perturbation of rank
at most the original rank forces an essential row or column. -/
theorem essential_row_or_column_of_rank_single [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (i : m) (j : n) (t : R) (ht : t ≠ 0)
    (hrank : (A + Matrix.single i j t).rank ≤ A.rank) :
    (A.submatrix (Subtype.val : {a : m // a ≠ i} → m) id).rank + 1 = A.rank ∨
      (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank + 1 = A.rank := by
  have h := essential_row_or_column_of_column_perturbation A
    (A + Matrix.single i j t) i j t ht hrank
    (fun c hc => by ext a; simp [Matrix.col_apply, Ne.symm hc])
    (by
      ext a
      by_cases ha : a = i
      · subst a
        simp [Matrix.col_apply]
      · simp [Matrix.col_apply, ha, Ne.symm ha])
  exact h.imp (rank_deleteRow_add_one_of_lt A i) (rank_deleteColumn_add_one_of_lt A j)

end IV01
