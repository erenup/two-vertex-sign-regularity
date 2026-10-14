import IV01.EssentialRank
import IV01.RankMinors
import IV01.SchurRank

set_option backward.isDefEq.respectTransparency false

namespace IV01

open Matrix Module

theorem matrix_eq_zero_of_rank_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (hA : A.rank = 0) : A = 0 := by
  ext i j
  by_contra h
  have hd : (A.submatrix (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)).det ≠ 0 := by
    simpa [Matrix.det_unique] using h
  have hr := Matrix.rank_of_det_ne_zero hd
  have hle := A.rank_submatrix_le (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  rw [hr, hA] at hle
  norm_num at hle

theorem columnSpace_eq_of_column_rank_eq {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (A : Matrix m n ℝ) (cols : p → n)
    (hrank : (A.submatrix id cols).rank = A.rank) :
    columnSpace (A.submatrix id cols) = columnSpace A := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact col_mem_columnSpace A (cols i)
  · simpa only [← rank_eq_finrank_columnSpace] using hrank

/-- A column basis preserves every row-restriction rank. -/
theorem rank_row_restrict_of_column_rank_eq {m n p r : Type*}
    [Fintype m] [Fintype n] [Fintype p] [Fintype r]
    (A : Matrix m n ℝ) (cols : p → n) (rows : r → m)
    (hrank : (A.submatrix id cols).rank = A.rank) :
    (A.submatrix rows cols).rank = (A.submatrix rows id).rank := by
  let π : (m → ℝ) →ₗ[ℝ] (r → ℝ) := LinearMap.funLeft ℝ ℝ rows
  have hmap (B : Matrix m n ℝ) :
      (columnSpace B).map π = columnSpace (B.submatrix rows id) := by
    simp only [columnSpace, Submodule.map_span, ← Set.range_comp]
    rfl
  have hmap' : (columnSpace (A.submatrix id cols)).map π =
      columnSpace (A.submatrix rows cols) := by
    simp only [columnSpace, Submodule.map_span, ← Set.range_comp]
    rfl
  have h := congrArg (Submodule.map π) (columnSpace_eq_of_column_rank_eq A cols hrank)
  rw [hmap', hmap] at h
  simp only [rank_eq_finrank_columnSpace]
  exact congrArg (fun P : Submodule ℝ (r → ℝ) => finrank ℝ P) h

/-- Every full-rank selected column family contains an essential column. -/
theorem essential_column_mem_range {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    (A : Matrix m n ℝ) (cols : p → n) (j : n)
    (hrank : (A.submatrix id cols).rank = A.rank)
    (hessential : (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank < A.rank) :
    j ∈ Set.range cols := by
  by_contra hmem
  let lift : p → {b : n // b ≠ j} := fun i => ⟨cols i, fun hi => hmem ⟨i, hi⟩⟩
  have hle := (A.submatrix id (Subtype.val : {b : n // b ≠ j} → n)).rank_submatrix_le id lift
  change (A.submatrix id cols).rank ≤ _ at hle
  rw [hrank] at hle
  omega

theorem schurAt_eq_zero_of_rank_bound {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0)
    (hrank : (M.submatrix (appendIndices P R) (appendIndices Q C)).rank ≤ p) :
    schurAt M P Q R C = 0 := by
  rw [schurAt_rank M P Q R C hH] at hrank
  exact matrix_eq_zero_of_rank_zero _ (by omega)

end IV01
