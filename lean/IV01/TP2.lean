import IV01.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Preorder.Finite

/-!
# Elementary consequences of nonnegative order-two minors

The rectangular predicates work on arbitrary linearly ordered index types.
The determinant result is Section 6.1 of the written IV-01 proof. The zero
propagation results are the staircase-support consequences used in Section 7.
-/

namespace IV01

def NonnegativeEntries {ι κ : Type*} (Y : Matrix ι κ ℝ) : Prop :=
  ∀ i j, 0 ≤ Y i j

def TP2 {ι κ : Type*} [Preorder ι] [Preorder κ]
    (Y : Matrix ι κ ℝ) : Prop :=
  ∀ i j k l, i < j → k < l →
    0 ≤ Y i k * Y j l - Y i l * Y j k

theorem NonnegativeEntries.submatrix {ι κ ρ σ : Type*}
    {Y : Matrix ι κ ℝ} (hY : NonnegativeEntries Y)
    (rows : ρ → ι) (cols : σ → κ) :
    NonnegativeEntries (Y.submatrix rows cols) :=
  fun i j => hY (rows i) (cols j)

theorem TP2.submatrix {ι κ ρ σ : Type*}
    [Preorder ι] [Preorder κ] [Preorder ρ] [Preorder σ]
    {Y : Matrix ι κ ℝ} (hY : TP2 Y)
    {rows : ρ → ι} {cols : σ → κ}
    (hr : StrictMono rows) (hc : StrictMono cols) :
    TP2 (Y.submatrix rows cols) :=
  fun i j k l hij hkl => hY (rows i) (rows j) (cols k) (cols l)
    (hr hij) (hc hkl)

theorem NonnegativeEntries.transpose {ι κ : Type*}
    {Y : Matrix ι κ ℝ} (hY : NonnegativeEntries Y) :
    NonnegativeEntries Y.transpose :=
  fun i j => hY j i

theorem TP2.transpose {ι κ : Type*} [Preorder ι] [Preorder κ]
    {Y : Matrix ι κ ℝ} (hY : TP2 Y) : TP2 Y.transpose := by
  intro i j k l hij hkl
  simpa only [Matrix.transpose_apply, mul_comm] using hY k l i j hkl hij

/-- A nonnegative TP2 three-square matrix with any middle-column zero
has nonnegative determinant. -/
theorem det_nonneg_of_middle_column_zero {Y : Square 3}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hz : ∃ i, Y i 1 = 0) : 0 ≤ Matrix.det Y := by
  have h₀₁ := h₂ 0 1 0 1 (by decide) (by decide)
  have h₁₂ := h₂ 1 2 1 2 (by decide) (by decide)
  by_cases he : Y 1 1 = 0
  · have hbd : Y 0 1 * Y 1 0 = 0 := by
      have := mul_nonneg (hY 0 1) (hY 1 0)
      rw [he] at h₀₁
      nlinarith
    have hfh : Y 1 2 * Y 2 1 = 0 := by
      have := mul_nonneg (hY 1 2) (hY 2 1)
      rw [he] at h₁₂
      nlinarith
    have hd : Matrix.det Y =
        Y 0 1 * Y 1 2 * Y 2 0 + Y 0 2 * Y 1 0 * Y 2 1 := by
      rw [Matrix.det_fin_three, he]
      have hbd' := congrArg (fun x : ℝ => x * Y 2 2) hbd
      have hfh' := congrArg (fun x : ℝ => Y 0 0 * x) hfh
      nlinarith
    rw [hd]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (hY 0 1) (hY 1 2)) (hY 2 0))
      (mul_nonneg (mul_nonneg (hY 0 2) (hY 1 0)) (hY 2 1))
  · have hepos : 0 < Y 1 1 := lt_of_le_of_ne (hY 1 1) (Ne.symm he)
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · change Y 0 1 = 0 at hi
      have hc : Y 0 2 = 0 := by
        have h := h₂ 0 1 1 2 (by decide) (by decide)
        rw [hi] at h
        nlinarith [hY 0 2]
      calc
        0 ≤ Y 0 0 * (Y 1 1 * Y 2 2 - Y 1 2 * Y 2 1) :=
          mul_nonneg (hY 0 0) h₁₂
        _ = Matrix.det Y := by rw [Matrix.det_fin_three, hi, hc]; ring
    · change Y 1 1 = 0 at hi
      exact (he hi).elim
    · change Y 2 1 = 0 at hi
      have hg : Y 2 0 = 0 := by
        have h := h₂ 1 2 0 1 (by decide) (by decide)
        rw [hi] at h
        nlinarith [hY 2 0]
      calc
        0 ≤ Y 2 2 * (Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0) :=
          mul_nonneg (hY 2 2) h₀₁
        _ = Matrix.det Y := by rw [Matrix.det_fin_three, hi, hg]; ring

/-- A negative TP2 three-minor has a strictly positive middle column. -/
theorem middle_column_pos_of_det_neg {Y : Square 3}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdet : Matrix.det Y < 0) : ∀ i, 0 < Y i 1 := by
  intro i
  by_contra h
  have hi : Y i 1 = 0 := le_antisymm (le_of_not_gt h) (hY i 1)
  have := det_nonneg_of_middle_column_zero hY h₂ ⟨i, hi⟩
  linarith

/-- The same middle-column conclusion for any increasing three-row,
three-column submatrix of a rectangular TP2 matrix. -/
theorem middle_column_pos_of_three_minor_neg {ι κ : Type*}
    [Preorder ι] [Preorder κ] {Y : Matrix ι κ ℝ}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    {rows : Fin 3 → ι} {cols : Fin 3 → κ}
    (hr : StrictMono rows) (hc : StrictMono cols)
    (hdet : Matrix.det (Y.submatrix rows cols) < 0) :
    ∀ i, 0 < Y (rows i) (cols 1) :=
  middle_column_pos_of_det_neg (hY.submatrix rows cols)
    (h₂.submatrix hr hc) hdet

private def permutationScore {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℤ :=
  ∑ i, (i.val : ℤ) * ((σ i).val : ℤ)

private theorem permutationScore_swap {n : ℕ} (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) :
    permutationScore (σ * Equiv.swap i j) - permutationScore σ =
      ((j.val : ℤ) - i.val) * (((σ i).val : ℤ) - (σ j).val) := by
  classical
  unfold permutationScore
  rw [← Finset.sum_sub_distrib]
  have hsum :
      (∑ k : Fin n, ((k.val : ℤ) * (((σ * Equiv.swap i j) k).val : ℤ) -
        (k.val : ℤ) * ((σ k).val : ℤ))) =
      ∑ k : Fin n,
        ((if k = i then (i.val : ℤ) * ((σ j).val : ℤ) -
          (i.val : ℤ) * ((σ i).val : ℤ) else 0) +
        (if k = j then (j.val : ℤ) * ((σ i).val : ℤ) -
          (j.val : ℤ) * ((σ j).val : ℤ) else 0)) := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k = i
    · subst k
      simp [Equiv.Perm.mul_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [Equiv.Perm.mul_apply, hij.symm]
      · simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj,
          hki, hkj]
  rw [hsum, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Nonsingularity provides a positive permutation-supported product. -/
theorem exists_positive_permutation {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (hdet : Matrix.det Y ≠ 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < Y (σ i) i := by
  classical
  rw [Matrix.det_apply'] at hdet
  obtain ⟨σ, _, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hdet
  refine ⟨σ, fun i => ?_⟩
  have hp : (∏ j, Y (σ j) j) ≠ 0 := (mul_ne_zero_iff.mp hσ).2
  have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
  exact lt_of_le_of_ne (hY (σ i) i) (Ne.symm hi)

/-- A positive permutation support can be uncrossed. Maximizing the exact
integer rearrangement score forces a supported permutation to be the identity. -/
theorem diagonal_pos_of_positive_permutation {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hex : ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < Y (σ i) i) :
    ∀ i, 0 < Y i i := by
  classical
  let good : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => ∀ i, 0 < Y (σ i) i)
  have hgood : good.Nonempty := by
    obtain ⟨σ, hσ⟩ := hex
    exact ⟨σ, by simpa [good] using hσ⟩
  obtain ⟨σ, hσgood, hmax⟩ := good.exists_max_image permutationScore hgood
  have hσ : ∀ i, 0 < Y (σ i) i := by simpa [good] using hσgood
  have hmono : StrictMono σ := by
    intro i j hij
    by_contra h
    have hrev : σ j < σ i := lt_of_le_of_ne (le_of_not_gt h)
      (fun hji => hij.ne (σ.injective hji.symm))
    have hminor := h₂ (σ j) (σ i) i j hrev hij
    have hcross : 0 < Y (σ j) j * Y (σ i) i := mul_pos (hσ j) (hσ i)
    have hnew₁ : 0 < Y (σ j) i := by
      by_contra h
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) (hY (σ i) j)
      linarith
    have hnew₂ : 0 < Y (σ i) j := by
      by_contra h
      have := mul_nonpos_of_nonneg_of_nonpos (hY (σ j) i) (le_of_not_gt h)
      linarith
    have hswap : σ * Equiv.swap i j ∈ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      intro k
      by_cases hki : k = i
      · subst k
        simpa [Equiv.Perm.mul_apply] using hnew₁
      · by_cases hkj : k = j
        · subst k
          simpa [Equiv.Perm.mul_apply] using hnew₂
        · simpa [Equiv.Perm.mul_apply,
            Equiv.swap_apply_of_ne_of_ne hki hkj] using hσ k
    have hle := hmax _ hswap
    have hscore := permutationScore_swap σ hij.ne
    have hij' : (i.val : ℤ) < j.val := by exact_mod_cast hij
    have hrev' : ((σ j).val : ℤ) < (σ i).val := by exact_mod_cast hrev
    have hpos := mul_pos (sub_pos.mpr hij') (sub_pos.mpr hrev')
    linarith
  have hid : (σ : Fin n → Fin n) = id := hmono.eq_id
  intro i
  simpa only [hid, id_eq] using hσ i

/-- Every diagonal entry of a nonsingular nonnegative TP2 matrix is positive. -/
theorem diagonal_pos_of_nonsingular {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0) :
    ∀ i, 0 < Y i i :=
  diagonal_pos_of_positive_permutation hY h₂ (exists_positive_permutation hY hdet)

section Staircase

variable {ι : Type*} [LinearOrder ι] {Y : Matrix ι ι ℝ}

/-- An above-diagonal zero propagates through its northeast rectangle. -/
theorem northeast_zero (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) {i j : ι}
    (hij : i < j) (hz : Y i j = 0)
    {r c : ι} (hri : r ≤ i) (hjc : j ≤ c) : Y r c = 0 := by
  have hic : Y i c = 0 := by
    rcases eq_or_lt_of_le hjc with rfl | hjc
    · exact hz
    · have h := h₂ i j j c hij hjc
      rw [hz] at h
      nlinarith [hY i c, hdiag j]
  rcases eq_or_lt_of_le hri with rfl | hri
  · exact hic
  · have h := h₂ r i i c hri (lt_of_lt_of_le hij hjc)
    rw [hic] at h
    nlinarith [hY r c, hdiag i]

/-- A below-diagonal zero propagates through its southwest rectangle. -/
theorem southwest_zero (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) {i j : ι}
    (hji : j < i) (hz : Y i j = 0)
    {r c : ι} (hir : i ≤ r) (hcj : c ≤ j) : Y r c = 0 := by
  exact northeast_zero hY.transpose h₂.transpose hdiag hji hz hcj hir

/-- If a row vanishes to the left of a positive entry, it vanishes at
every earlier column. -/
theorem row_zero_left_of_pos_right
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) {i a b q : ι}
    (hab : a ≤ b) (hbq : b < q) (hb : Y i b = 0)
    (hq : 0 < Y i q) : Y i a = 0 := by
  have hbi : b < i := by
    by_contra h
    rcases eq_or_lt_of_le (le_of_not_gt h) with rfl | hib
    · have := hdiag i
      linarith
    · have hz := northeast_zero hY h₂ hdiag hib hb le_rfl (le_of_lt hbq)
      linarith
  exact southwest_zero hY h₂ hdiag hbi hb le_rfl hab

/-- If a row vanishes to the right of a positive entry, it vanishes at
every later column. -/
theorem row_zero_right_of_pos_left
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) {i q b c : ι}
    (hqb : q < b) (hbc : b ≤ c) (hb : Y i b = 0)
    (hq : 0 < Y i q) : Y i c = 0 := by
  have hib : i < b := by
    by_contra h
    rcases eq_or_lt_of_le (le_of_not_gt h) with rfl | hbi
    · have := hdiag b
      linarith
    · have hz := southwest_zero hY h₂ hdiag hbi hb le_rfl (le_of_lt hqb)
      linarith
  exact northeast_zero hY h₂ hdiag hib hb le_rfl hbc

/-- The left outer column in Section 7 vanishes on all selected rows.
The statement allows any family of selected rows, including three rows. -/
theorem zero_column_left_of_zero_column_of_pos_right {ρ : Type*}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) (rows : ρ → ι) {a b q : ι}
    (hab : a ≤ b) (hbq : b < q)
    (hb : ∀ r, Y (rows r) b = 0) (hq : ∀ r, 0 < Y (rows r) q) :
    ∀ r, Y (rows r) a = 0 :=
  fun r => row_zero_left_of_pos_right hY h₂ hdiag hab hbq (hb r) (hq r)

/-- The corresponding right outer column vanishes on all selected rows. -/
theorem zero_column_right_of_zero_column_of_pos_left {ρ : Type*}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y)
    (hdiag : ∀ i, 0 < Y i i) (rows : ρ → ι) {q b c : ι}
    (hqb : q < b) (hbc : b ≤ c)
    (hb : ∀ r, Y (rows r) b = 0) (hq : ∀ r, 0 < Y (rows r) q) :
    ∀ r, Y (rows r) c = 0 :=
  fun r => row_zero_right_of_pos_left hY h₂ hdiag hqb hbc (hb r) (hq r)

end Staircase

end IV01
