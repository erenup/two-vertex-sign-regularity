import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace IV01

open Matrix Module

variable {R : Type*} [Field R]

/-- Restricting to an injective row family loses at most the number of omitted rows. -/
theorem rank_add_card_le_rank_submatrix_rows_add_card
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n R) (rows : p → m) (hrows : Function.Injective rows) :
    A.rank + Fintype.card p ≤ (A.submatrix rows id).rank + Fintype.card m := by
  classical
  let P : Submodule R (n → R) := Submodule.span R (Set.range (A.submatrix rows id).row)
  let Q : Submodule R (n → R) :=
    Submodule.span R (Set.range (fun a : {i : m // i ∉ Set.range rows} => A.row a.val))
  have hspan : Submodule.span R (Set.range A.row) ≤ P ⊔ Q := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    by_cases hi : i ∈ Set.range rows
    · obtain ⟨a, rfl⟩ := hi
      apply Submodule.mem_sup_left
      exact Submodule.subset_span ⟨a, rfl⟩
    · apply Submodule.mem_sup_right
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have hdim : A.rank ≤ finrank R P + finrank R Q := by
    rw [Matrix.rank_eq_finrank_span_row]
    exact (Submodule.finrank_mono hspan).trans (Submodule.finrank_add_le_finrank_add_finrank P Q)
  have hQ : finrank R Q ≤ Fintype.card {i : m // i ∉ Set.range rows} :=
    finrank_range_le_card _
  have hcard : Fintype.card {i : m // i ∉ Set.range rows} =
      Fintype.card m - Fintype.card p := by
    rw [Fintype.card_subtype_compl]
    have hc : Fintype.card (Set.range rows) = Fintype.card p :=
      (Fintype.card_congr (Equiv.ofInjective rows hrows)).symm
    rw [hc]
  have hp : finrank R P = (A.submatrix rows id).rank :=
    (Matrix.rank_eq_finrank_span_row _).symm
  have hle := Fintype.card_le_of_injective rows hrows
  rw [hcard] at hQ
  rw [hp] at hdim
  omega

/-- Restricting to an injective column family loses at most the number omitted. -/
theorem rank_add_card_le_rank_submatrix_cols_add_card
    {m n q : Type*} [Fintype m] [Fintype n] [Fintype q]
    (A : Matrix m n R) (cols : q → n) (hcols : Function.Injective cols) :
    A.rank + Fintype.card q ≤ (A.submatrix id cols).rank + Fintype.card n := by
  have h := rank_add_card_le_rank_submatrix_rows_add_card Aᵀ cols hcols
  rw [Matrix.rank_transpose, ← Matrix.transpose_submatrix, Matrix.rank_transpose] at h
  exact h

/-- The generic dimension bound for an arbitrary rectangular submatrix. -/
theorem rank_add_cards_le_submatrix_rank_add_cards
    {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype q]
    (A : Matrix m n R) (rows : p → m) (cols : q → n)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols) :
    A.rank + Fintype.card p + Fintype.card q ≤
      (A.submatrix rows cols).rank + Fintype.card m + Fintype.card n := by
  have hr := rank_add_card_le_rank_submatrix_rows_add_card A rows hrows
  have hc := rank_add_card_le_rank_submatrix_cols_add_card (A.submatrix rows id) cols hcols
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp] at hc
  omega

/-- In an invertible square matrix, a `p × q` submatrix has rank at least `p+q-N`. -/
theorem cards_le_submatrix_rank_add_card_of_det_ne_zero
    {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n]
    (A : Matrix n n R) (hA : A.det ≠ 0) (rows : p → n) (cols : q → n)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols) :
    Fintype.card p + Fintype.card q ≤ (A.submatrix rows cols).rank + Fintype.card n := by
  have h := rank_add_cards_le_submatrix_rank_add_cards A rows cols hrows hcols
  rw [Matrix.rank_of_det_ne_zero hA] at h
  omega

/-- A rank-at-most-one submatrix of an invertible matrix has `p+q ≤ N+1`. -/
theorem cards_le_card_add_one_of_submatrix_rank_le_one
    {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n]
    (A : Matrix n n R) (hA : A.det ≠ 0) (rows : p → n) (cols : q → n)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hrank : (A.submatrix rows cols).rank ≤ 1) :
    Fintype.card p + Fintype.card q ≤ Fintype.card n + 1 := by
  have h := cards_le_submatrix_rank_add_card_of_det_ne_zero A hA rows cols hrows hcols
  omega

/-- The corner-size bound in the form supplied by an outer-product factorization. -/
theorem cards_le_card_add_one_of_submatrix_outer_product
    {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n]
    (A : Matrix n n R) (hA : A.det ≠ 0) (rows : p → n) (cols : q → n)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (hf : ∃ (u : p → R) (v : q → R), ∀ i j, A (rows i) (cols j) = u i * v j) :
    Fintype.card p + Fintype.card q ≤ Fintype.card n + 1 := by
  obtain ⟨u, v, huv⟩ := hf
  apply cards_le_card_add_one_of_submatrix_rank_le_one A hA rows cols hrows hcols
  have heq : A.submatrix rows cols = Matrix.vecMulVec u v := by
    ext i j
    exact huv i j
  rw [heq]
  exact Matrix.rank_vecMulVec_le u v

end IV01
