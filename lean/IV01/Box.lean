import IV01.InteriorZero

namespace IV01

theorem signature_ne_zero {n k : ℕ} {ε : ℕ → ℝ}
    (hε : IsSignature n ε) (hk : 1 ≤ k) (hkn : k ≤ n) : ε k ≠ 0 := by
  rcases hε k hk hkn with h | h <;> simp [h]

theorem checkerMinus_mem_box {n : ℕ} {L U : Square n} (hLU : EntrywiseLE L U) :
    InBox L U (checkerMinus L U) := by
  constructor <;> intro i j <;> dsimp [checkerMinus] <;>
    split_ifs <;> first | exact hLU i j | exact le_rfl

theorem checkerPlus_mem_box {n : ℕ} {L U : Square n} (hLU : EntrywiseLE L U) :
    InBox L U (checkerPlus L U) := by
  constructor <;> intro i j <;> dsimp [checkerPlus] <;>
    split_ifs <;> first | exact hLU i j | exact le_rfl

noncomputable def boxMidpoint {n : ℕ} (L U : Square n) : Square n :=
  fun i j => (L i j + U i j) / 2

theorem boxMidpoint_interior {n : ℕ} {L U : Square n} (hLU : EntrywiseLE L U) :
    InRelativeInterior L U (boxMidpoint L U) := by
  constructor
  · constructor <;> intro i j <;> dsimp [boxMidpoint] <;> have := hLU i j <;> linarith
  · intro i j hij
    dsimp [boxMidpoint]
    constructor <;> linarith

theorem checker_midpoint_eq {n : ℕ} (L U : Square n) :
    boxMidpoint (checkerMinus L U) (checkerPlus L U) = boxMidpoint L U := by
  ext i j
  dsimp [boxMidpoint, checkerMinus, checkerPlus]
  split_ifs <;> ring

theorem checker_eq_of_fixed {n : ℕ} {L U : Square n} {i j : Fin n}
    (h : L i j = U i j) : checkerMinus L U i j = checkerPlus L U i j := by
  simp [checkerMinus, checkerPlus, h]

theorem SignRegular.entry {n : ℕ} {ε : ℕ → ℝ} {M : Square n}
    (hM : SignRegular ε M) (i j : Fin n) : 0 ≤ ε 1 * M i j := by
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hi : StrictMono (fun _ : Fin 1 => i) := by
    intro a b hab
    have heq : a = b := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hab) heq)
  have hj : StrictMono (fun _ : Fin 1 => j) := by
    intro a b hab
    have heq : a = b := Subsingleton.elim _ _
    exact False.elim ((ne_of_lt hab) heq)
  simpa [minor, Matrix.det_unique] using hM 1 le_rfl hn _ _ hi hj

/-- Prescribed signs of all entries propagate to the whole interval. -/
theorem entry_sign_in_box {n : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hminus : SignRegular ε (checkerMinus L U))
    (hplus : SignRegular ε (checkerPlus L U))
    (hM : InBox L U M) (i j : Fin n) : 0 ≤ ε 1 * M i j := by
  have hL : 0 ≤ ε 1 * L i j := by
    have hm := hminus.entry i j
    have hp := hplus.entry i j
    dsimp [checkerMinus, checkerPlus] at hm hp
    split_ifs at hm hp <;> assumption
  have hU : 0 ≤ ε 1 * U i j := by
    have hm := hminus.entry i j
    have hp := hplus.entry i j
    dsimp [checkerMinus, checkerPlus] at hm hp
    split_ifs at hm hp <;> assumption
  by_cases hε : 0 ≤ ε 1
  · exact hL.trans (mul_le_mul_of_nonneg_left (hM.1 i j) hε)
  · exact hU.trans (mul_le_mul_of_nonpos_left (hM.2 i j) (le_of_not_ge hε))

/-- If all columns but one agree, the determinant is affine on the
segment between the two matrices. -/
theorem det_midpoint_of_eq_off_column {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (j : ι) (h : ∀ i k, k ≠ j → A i k = B i k) :
    Matrix.det (fun i k => (A i k + B i k) / 2) = (A.det + B.det) / 2 := by
  have hB : B = A.updateCol j (fun i => B i j) := by
    ext i k
    by_cases hk : k = j
    · simp [hk]
    · simp [Matrix.updateCol, Function.update_of_ne hk, ← h i k hk]
  have hmid : (fun i k => (A i k + B i k) / 2) =
      A.updateCol j ((1 / 2 : ℝ) • ((fun i => A i j) + (fun i => B i j))) := by
    ext i k
    by_cases hk : k = j
    · subst k
      simp [Matrix.updateCol_apply, smul_eq_mul] <;> ring
    · simp [Matrix.updateCol, Function.update_of_ne hk, ← h i k hk]
  rw [hmid, Matrix.det_updateCol_smul, Matrix.det_updateCol_add]
  have hA : A.updateCol j (fun i => A i j) = A := Matrix.updateCol_eq_self _ _
  rw [hA, ← hB]
  ring

/-- Section 7.1's midpoint argument, for a specified minor with only one
possibly varying selected column. Endpoint zeros then hold everywhere. -/
theorem fixed_columns_minor_zero_on_box {n k : ℕ} {L U : Square n}
    (hLU : EntrywiseLE L U) (rows cols : Fin k → Fin n)
    (hr : StrictMono rows) (hc : StrictMono cols) (j : Fin k)
    (hfixed : ∀ i c, c ≠ j → L (rows i) (cols c) = U (rows i) (cols c))
    (s : ℝ) (hs : s ≠ 0)
    (hnonneg : ∀ X, InBox L U X → 0 ≤ s * minor X rows cols)
    (hminus : minor (checkerMinus L U) rows cols = 0)
    (hplus : minor (checkerPlus L U) rows cols = 0)
    {X : Square n} (hX : InBox L U X) : minor X rows cols = 0 := by
  apply minor_zero_on_box rows cols hr hc s hs hnonneg (boxMidpoint_interior hLU) ?_ hX
  rw [← checker_midpoint_eq]
  unfold minor
  have h := det_midpoint_of_eq_off_column
    ((checkerMinus L U).submatrix rows cols) ((checkerPlus L U).submatrix rows cols) j
    (fun i c hci => checker_eq_of_fixed (hfixed i c hci))
  simp only [Matrix.submatrix_apply] at h
  change Matrix.det (fun i c =>
    (checkerMinus L U (rows i) (cols c) + checkerPlus L U (rows i) (cols c)) / 2) = 0
  rw [h]
  change (minor (checkerMinus L U) rows cols + minor (checkerPlus L U) rows cols) / 2 = 0
  rw [hminus, hplus]
  norm_num

end IV01
