import IV01.Definitions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Inverse-positive intervals

The nonsingularity argument is finite: a positive strict supersolution for
a nonnegative matrix excludes nonzero fixed vectors by a weighted maximum.
-/

namespace IV01

open Matrix
open scoped BigOperators

lemma weighted_fixed_vector_eq_zero {n : ℕ} (E : Square n)
    (v : Fin n → ℝ) (hE : ∀ i j, 0 ≤ E i j)
    (hv : ∀ i, 0 < v i) (hEv : ∀ i, (E *ᵥ v) i < v i)
    (x : Fin n → ℝ) (hx : E *ᵥ x = x) : x = 0 := by
  classical
  by_contra hx0
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    apply hx0
    ext j
    exact h j
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨j, Finset.mem_univ j⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun k => |x k| / v k) huniv
  let c : ℝ := |x i| / v i
  have hc : 0 < c := lt_of_lt_of_le (div_pos (abs_pos.mpr hj) (hv j))
    (hi j (Finset.mem_univ j))
  have hbound : ∀ k, |x k| ≤ c * v k := by
    intro k
    exact (div_le_iff₀ (hv k)).mp (hi k (Finset.mem_univ k))
  have hci : c * v i = |x i| := div_mul_cancel₀ _ (ne_of_gt (hv i))
  have heq : |x i| = |∑ k, E i k * x k| := by
    rw [← congrFun hx i]
    rfl
  have hlt : |x i| < |x i| := calc
    |x i| = |∑ k, E i k * x k| := heq
    _ ≤ ∑ k, |E i k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, E i k * |x k| := by simp_rw [abs_mul, abs_of_nonneg (hE i _)]
    _ ≤ ∑ k, E i k * (c * v k) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hbound k) (hE i k)
    _ = c * (E *ᵥ v) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      ext k
      ring
    _ < c * v i := mul_lt_mul_of_pos_left (hEv i) hc
    _ = |x i| := hci
  exact (lt_irrefl _ hlt)

lemma det_one_sub_ne_zero_of_positive_supersolution {n : ℕ} (E : Square n)
    (v : Fin n → ℝ) (hE : ∀ i j, 0 ≤ E i j)
    (hv : ∀ i, 0 < v i) (hEv : ∀ i, (E *ᵥ v) i < v i) :
    Matrix.det (1 - E) ≠ 0 := by
  apply (((1 - E).isUnit_iff_isUnit_det).mp ?_).ne_zero
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hker : (1 - E) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hfixed : E *ᵥ (x - y) = x - y := by
    exact (sub_eq_zero.mp (by
      simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hker)).symm
  have hz := weighted_fixed_vector_eq_zero E v hE hv hEv (x - y) hfixed
  exact sub_eq_zero.mp hz

lemma inv_mulVec_one_pos {n : ℕ} (P : Square n) (hP : P.det ≠ 0)
    (hnonneg : ∀ i j, 0 ≤ P⁻¹ i j) :
    ∀ i, 0 < (P⁻¹ *ᵥ (fun _ => 1)) i := by
  classical
  intro i
  have hex : ∃ j, 0 < P⁻¹ i j := by
    by_contra! h
    have hz : ∀ j, P⁻¹ i j = 0 := fun j => le_antisymm (h j) (hnonneg i j)
    have hid := congrArg (fun M : Square n => M i i)
      (Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hP))
    simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply_eq] at hid
    norm_num at hid
  obtain ⟨j, hj⟩ := hex
  simpa only [Matrix.mulVec, dotProduct, mul_one] using
    (Finset.sum_pos' (fun k _ => hnonneg i k) ⟨j, Finset.mem_univ j, hj⟩)

/-- Every matrix between two inverse-positive nonsingular endpoints is nonsingular.
All inequalities are entrywise; no symmetry or strict entry positivity is assumed. -/
theorem inverse_positive_interval_nonsingular {n : ℕ} (P C Q : Square n)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (hPinv : ∀ i j, 0 ≤ P⁻¹ i j) (hQinv : ∀ i j, 0 ≤ Q⁻¹ i j)
    (hPC : EntrywiseLE P C) (hCQ : EntrywiseLE C Q) : C.det ≠ 0 := by
  classical
  let v : Fin n → ℝ := P⁻¹ *ᵥ (fun _ => 1)
  let w : Fin n → ℝ := Q⁻¹ *ᵥ (fun _ => 1)
  let E : Square n := Q⁻¹ * (Q - C)
  let T : Square n := Q⁻¹ * (Q - P)
  have hv : ∀ i, 0 < v i := inv_mulVec_one_pos P hP hPinv
  have hw : ∀ i, 0 < w i := inv_mulVec_one_pos Q hQ hQinv
  have hE : ∀ i j, 0 ≤ E i j := by
    intro i j
    change 0 ≤ ∑ k, Q⁻¹ i k * (Q k j - C k j)
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (hQinv i k) (sub_nonneg.mpr (hCQ k j))
  have hET : ∀ i j, E i j ≤ T i j := by
    intro i j
    change (∑ k, Q⁻¹ i k * (Q k j - C k j)) ≤
      ∑ k, Q⁻¹ i k * (Q k j - P k j)
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hPC k j) _) (hQinv i k)
  have hTv : T *ᵥ v = v - w := by
    dsimp [T, v, w]
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ),
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_iff_ne_zero.mpr hP)]
  have hEv : ∀ i, (E *ᵥ v) i < v i := by
    intro i
    have hle : (E *ᵥ v) i ≤ (T *ᵥ v) i := by
      change (∑ k, E i k * v k) ≤ ∑ k, T i k * v k
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hET i k) (le_of_lt (hv k))
    rw [hTv] at hle
    exact lt_of_le_of_lt hle (sub_lt_self _ (hw i))
  have hdet := det_one_sub_ne_zero_of_positive_supersolution E v hE hv hEv
  have hfactor : 1 - E = Q⁻¹ * C := by
    dsimp [E]
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)]
    abel
  rw [hfactor, Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2

/-- Conjugation by the alternating-sign diagonal matrix. -/
def checkerConjugate {n : ℕ} (M : Square n) : Square n :=
  Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val) * M *
    Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val)

lemma checkerConjugate_apply {n : ℕ} (M : Square n) (i j : Fin n) :
    checkerConjugate M i j = (-1 : ℝ) ^ (i.val + j.val) * M i j := by
  simp only [checkerConjugate, Matrix.diagonal_mul, Matrix.mul_diagonal, pow_add]
  ring

lemma checkerDiagonal_square (n : ℕ) :
    (Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val)) *
      (Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have hs : ∀ i : Fin n, (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    intro i
    rcases neg_one_pow_eq_or ℝ i.val with h | h <;> simp [h]
  simp_rw [hs]
  exact Matrix.diagonal_one

lemma checkerConjugate_det {n : ℕ} (M : Square n) :
    (checkerConjugate M).det = M.det := by
  let D : Square n := Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val)
  have hd : D.det * D.det = 1 := by
    rw [← Matrix.det_mul]
    simpa only [Matrix.det_one] using congrArg Matrix.det (checkerDiagonal_square n)
  change (D * M * D).det = _
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    D.det * M.det * D.det = (D.det * D.det) * M.det := by ring
    _ = M.det := by rw [hd, one_mul]

lemma checkerConjugate_inv {n : ℕ} (M : Square n) :
    (checkerConjugate M)⁻¹ = checkerConjugate M⁻¹ := by
  let D : Square n := Matrix.diagonal (fun i : Fin n => (-1 : ℝ) ^ i.val)
  have hd : D⁻¹ = D := Matrix.inv_eq_left_inv (checkerDiagonal_square n)
  change (D * M * D)⁻¹ = D * M⁻¹ * D
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hd, Matrix.mul_assoc]

lemma checkerConjugate_inv_cofactor {n : ℕ} (M : Square (n + 1))
    (i j : Fin (n + 1)) :
    checkerConjugate M⁻¹ i j =
      M.det⁻¹ * (M.submatrix j.succAbove i.succAbove).det := by
  rw [checkerConjugate_apply, Matrix.inv_def, Matrix.smul_apply,
    smul_eq_mul, Ring.inverse_eq_inv, Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [Nat.add_comm j.val i.val]
  have hs : (-1 : ℝ) ^ (i.val + j.val) * (-1 : ℝ) ^ (i.val + j.val) = 1 := by
    rcases neg_one_pow_eq_or ℝ (i.val + j.val) with h | h <;> simp [h]
  calc
    _ = ((-1 : ℝ) ^ (i.val + j.val) * (-1 : ℝ) ^ (i.val + j.val)) *
      (M.det⁻¹ * (M.submatrix j.succAbove i.succAbove).det) := by ring
    _ = _ := by rw [hs, one_mul]

lemma signed_checker_inverse_nonneg {n : ℕ} {ε : ℕ → ℝ}
    (M : Square (n + 2)) (hsig : IsSignature (n + 2) ε)
    (hSR : SignRegular ε M) :
    ∀ i j, 0 ≤ (ε (n + 1) * ε (n + 2)) * checkerConjugate M⁻¹ i j := by
  intro i j
  have hc : 0 ≤ ε (n + 1) * (M.submatrix j.succAbove i.succAbove).det :=
    hSR (n + 1) (by omega) (by omega) _ _
      (Fin.strictMono_succAbove j) (Fin.strictMono_succAbove i)
  have ht : 0 ≤ ε (n + 2) * M.det := by
    simpa only [minor, Matrix.submatrix_id_id] using
      hSR (n + 2) (by omega) le_rfl id id strictMono_id strictMono_id
  have hr : 0 ≤ ε (n + 2) / M.det := by
    rcases hsig (n + 2) (by omega) le_rfl with h | h
    · rw [h] at ht ⊢
      exact div_nonneg (by norm_num) (by simpa using ht)
    · rw [h] at ht ⊢
      exact div_nonneg_of_nonpos (by norm_num) (by linarith)
  rw [checkerConjugate_inv_cofactor]
  have heq : ε (n + 1) * ε (n + 2) *
      (M.det⁻¹ * (M.submatrix j.succAbove i.succAbove).det) =
      (ε (n + 1) * (M.submatrix j.succAbove i.succAbove).det) *
        (ε (n + 2) / M.det) := by ring
  rw [heq]
  exact mul_nonneg hc hr

lemma det_neg_ne_zero {n : ℕ} {M : Square n} (h : M.det ≠ 0) : (-M).det ≠ 0 := by
  rw [Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h

lemma inverse_neg {n : ℕ} (M : Square n) (h : M.det ≠ 0) : (-M)⁻¹ = -M⁻¹ := by
  apply Matrix.inv_eq_left_inv
  simpa only [neg_mul_neg] using Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr h)

/-- The checker-order interval between nonsingular sign-regular endpoints
has no singular matrices. This lemma covers dimensions at least two. -/
theorem checker_interval_nonsingular {n : ℕ} {ε : ℕ → ℝ}
    (A X B : Square (n + 2)) (hsig : IsSignature (n + 2) ε)
    (hA : NonsingularSignRegular ε A) (hB : NonsingularSignRegular ε B)
    (hAX : EntrywiseLE (checkerConjugate A) (checkerConjugate X))
    (hXB : EntrywiseLE (checkerConjugate X) (checkerConjugate B)) : X.det ≠ 0 := by
  have hAd : (checkerConjugate A).det ≠ 0 := by
    simpa only [checkerConjugate_det] using hA.1
  have hBd : (checkerConjugate B).det ≠ 0 := by
    simpa only [checkerConjugate_det] using hB.1
  have hAi := signed_checker_inverse_nonneg A hsig hA.2
  have hBi := signed_checker_inverse_nonneg B hsig hB.2
  have hd : ε (n + 1) * ε (n + 2) = 1 ∨ ε (n + 1) * ε (n + 2) = -1 := by
    rcases hsig (n + 1) (by omega) (by omega) with h₁ | h₁ <;>
      rcases hsig (n + 2) (by omega) le_rfl with h₂ | h₂ <;>
        simp [h₁, h₂]
  rcases hd with hd | hd
  · have h := inverse_positive_interval_nonsingular
      (checkerConjugate A) (checkerConjugate X) (checkerConjugate B) hAd hBd
      (by simpa only [checkerConjugate_inv, hd, one_mul] using hAi)
      (by simpa only [checkerConjugate_inv, hd, one_mul] using hBi) hAX hXB
    rwa [checkerConjugate_det] at h
  · have h := inverse_positive_interval_nonsingular
      (-checkerConjugate B) (-checkerConjugate X) (-checkerConjugate A)
      (det_neg_ne_zero hBd) (det_neg_ne_zero hAd)
      (by simpa only [inverse_neg _ hBd, checkerConjugate_inv, hd, neg_one_mul,
        Matrix.neg_apply] using hBi)
      (by simpa only [inverse_neg _ hAd, checkerConjugate_inv, hd, neg_one_mul,
        Matrix.neg_apply] using hAi)
      (fun i j => neg_le_neg (hXB i j)) (fun i j => neg_le_neg (hAX i j))
    rw [Matrix.det_neg, checkerConjugate_det] at h
    exact (mul_ne_zero_iff.mp h).2

lemma checker_sign_eq (k : ℕ) :
    (-1 : ℝ) ^ k = if k % 2 = 0 then 1 else -1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases h : k % 2 = 0
  · simp [h]
  · have h1 : k % 2 = 1 := by omega
    simp [h1]

lemma checkerConjugate_box_bounds {n : ℕ} {L U X : Square n}
    (hX : InBox L U X) :
    EntrywiseLE (checkerConjugate (checkerMinus L U)) (checkerConjugate X) ∧
      EntrywiseLE (checkerConjugate X) (checkerConjugate (checkerPlus L U)) := by
  constructor <;> intro i j <;>
    simp only [checkerConjugate_apply, checker_sign_eq, checkerMinus, checkerPlus] <;>
    split_ifs <;> simp only [one_mul, neg_one_mul, neg_le_neg_iff]
  · exact hX.1 i j
  · exact hX.2 i j
  · exact hX.2 i j
  · exact hX.1 i j

/-- Section 2.1 of the paper, with exactly the box and endpoint predicates
used in the accepted theorem statement. It includes the empty and scalar cases. -/
theorem inBox_nonsingular {n : ℕ} {ε : ℕ → ℝ} {L U X : Square n}
    (hsig : IsSignature n ε)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (hX : InBox L U X) : X.det ≠ 0 := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · have hl : 0 ≤ ε 1 * L 0 0 := by
      simpa [minor, Matrix.det_unique, checkerMinus] using
        hminus.2 1 le_rfl le_rfl id id strictMono_id strictMono_id
    have hu : 0 ≤ ε 1 * U 0 0 := by
      simpa [minor, Matrix.det_unique, checkerPlus] using
        hplus.2 1 le_rfl le_rfl id id strictMono_id strictMono_id
    have hl0 : L 0 0 ≠ 0 := by
      simpa [Matrix.det_unique, checkerMinus] using hminus.1
    have hu0 : U 0 0 ≠ 0 := by
      simpa [Matrix.det_unique, checkerPlus] using hplus.1
    have hlX := hX.1 0 0
    have hXU := hX.2 0 0
    change X.det ≠ 0
    rw [Matrix.det_fin_one]
    rcases hsig 1 le_rfl le_rfl with h | h
    · rw [h, one_mul] at hl
      exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne hl (Ne.symm hl0)) hlX)
    · rw [h, neg_one_mul] at hu
      exact ne_of_lt (lt_of_le_of_lt hXU (lt_of_le_of_ne (by linarith) hu0))
  · obtain ⟨hAX, hXB⟩ := checkerConjugate_box_bounds hX
    exact checker_interval_nonsingular _ X _ hsig hminus hplus hAX hXB

end IV01
