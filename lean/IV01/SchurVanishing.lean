import IV01.RankRestriction
import IV01.SchurClosure

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem rank_submatrix_le_of_ranges {n : ℕ} {α β ρ κ : Type*}
    [Fintype α] [Fintype β] [Fintype ρ] [Fintype κ]
    (M : Square n) (rows : α → Fin n) (cols : β → Fin n)
    (r : ρ → Fin n) (c : κ → Fin n)
    (hr : ∀ i, r i ∈ Set.range rows) (hc : ∀ j, c j ∈ Set.range cols) :
    (M.submatrix r c).rank ≤ (M.submatrix rows cols).rank := by
  choose rr hrr using hr
  choose cc hcc using hc
  have h := (M.submatrix rows cols).rank_submatrix_le rr cc
  have heq : (M.submatrix rows cols).submatrix rr cc = M.submatrix r c := by
    ext i j
    simp only [Matrix.submatrix_apply, hrr, hcc]
  rwa [heq] at h

theorem schurAt_entry_zero_of_rectangle_rank {n p m : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n)
    (rows : α → Fin n) (cols : β → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0) (hrank : (M.submatrix rows cols).rank ≤ p)
    (hP : ∀ i, P i ∈ Set.range rows) (hQ : ∀ i, Q i ∈ Set.range cols)
    (i j : Fin m) (hi : R i ∈ Set.range rows) (hj : C j ∈ Set.range cols) :
    schurAt M P Q R C i j = 0 := by
  have hz := schurAt_eq_zero_of_rank_bound M P Q (fun _ : Fin 1 => R i)
    (fun _ : Fin 1 => C j) hH (by
      apply (rank_submatrix_le_of_ranges M rows cols _ _ ?_ ?_).trans hrank
      · intro a
        unfold appendIndices
        cases finSumFinEquiv.symm a with
        | inl a => exact hP a
        | inr a => exact hi
      · intro a
        unfold appendIndices
        cases finSumFinEquiv.symm a with
        | inl a => exact hQ a
        | inr a => exact hj)
  have hval := congrArg (fun Z : Matrix (Fin 1) (Fin 1) ℝ => Z 0 0) hz
  have hsub := schurAt_submatrix M P Q R C (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)
  have heval := congrArg (fun Z : Matrix (Fin 1) (Fin 1) ℝ => Z 0 0) hsub
  exact heval.trans hval

theorem normalizedSchur_entry_zero {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (i j : Fin m) (hz : schurAt M P Q R C i j = 0) :
    normalizedSchur M P Q R C e e₁ e₂ (if e * e₂ = 1 then i else i.rev) j = 0 := by
  unfold normalizedSchur
  split_ifs <;>
    simp [scalarNormalizedSchur, reverseRows, signedSchurAt,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hz]

theorem schurAt_entry_ne_zero_of_normalized {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (i j : Fin m)
    (hne : normalizedSchur M P Q R C e e₁ e₂
      (if e * e₂ = 1 then i else i.rev) j ≠ 0) :
    schurAt M P Q R C i j ≠ 0 := by
  intro hz
  exact hne (normalizedSchur_entry_zero M P Q R C e e₁ e₂ i j hz)

theorem normalizedSchur_selected_column_zero {n p m k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin k → Fin m) (j : Fin m)
    (hz : ∀ i, schurAt M P Q R C (rows i) j = 0) :
    ∀ i, normalizedSchur M P Q R C e e₁ e₂ (orientedRows rows e e₂ i) j = 0 := by
  intro i
  by_cases h : e * e₂ = 1
  · simpa [orientedRows, h] using
      normalizedSchur_entry_zero M P Q R C e e₁ e₂ (rows i) j (hz i)
  · simpa [orientedRows, h] using
      normalizedSchur_entry_zero M P Q R C e e₁ e₂ (rows i.rev) j (hz i.rev)

theorem no_negative_three_of_zero_interior_column {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Y.det ≠ 0)
    (rows cols : Fin 3 → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : minor Y rows cols < 0) (b : Fin n)
    (hleft : cols 0 < b) (hright : b < cols 2) (hbq : b ≠ cols 1)
    (hzero : ∀ i, Y (rows i) b = 0) : False := by
  have hpos := middle_column_pos_of_three_minor_neg hY h₂ hr hc hbad
  have hdiag := diagonal_pos_of_nonsingular hY h₂ hdet
  rcases lt_or_gt_of_ne hbq with hb | hb
  · have hz := zero_column_left_of_zero_column_of_pos_right hY h₂ hdiag rows
      hleft.le hb hzero hpos
    have heq : minor Y rows cols = 0 := Matrix.det_eq_zero_of_column_eq_zero 0 hz
    rw [heq] at hbad
    exact (lt_irrefl 0) hbad
  · have hz := zero_column_right_of_zero_column_of_pos_left hY h₂ hdiag rows
      hb hright.le hzero hpos
    have heq : minor Y rows cols = 0 := Matrix.det_eq_zero_of_column_eq_zero 2 hz
    rw [heq] at hbad
    exact (lt_irrefl 0) hbad

end IV01
