import IV01.SchurRank
import IV01.TP2

namespace IV01

open Matrix
open scoped BigOperators

/-- One specified order of minors has the indicated weak sign. No
hypothesis about any other order is included. -/
def HasSignedMinors {n : ℕ} (M : Square n) (k : ℕ) (s : ℝ) : Prop :=
  ∀ rows cols : Fin k → Fin n, StrictMono rows → StrictMono cols →
    0 ≤ s * minor M rows cols

lemma schurAt_submatrix {n p r c a b : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (rows : Fin a → Fin r) (cols : Fin b → Fin c) :
    (schurAt M P Q R C).submatrix rows cols =
      schurAt M P Q (R ∘ rows) (C ∘ cols) := rfl

lemma signedSchurAt_submatrix {n p r c a b : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (rows : Fin a → Fin r) (cols : Fin b → Fin c) :
    (signedSchurAt M P Q R C).submatrix rows cols =
      signedSchurAt M P Q (R ∘ rows) (C ∘ cols) := by
  ext i j
  simp only [signedSchurAt, Matrix.submatrix_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Function.comp_apply]
  rfl

/-- The prescribed sign of order `p+k` alone transfers to order `k`
of the signed Schur matrix. The pivot sign `e` is explicit, so the
empty pivot never imposes a condition on the unprescribed value `ε 0`. -/
theorem signedSchurAt_inherits_sign {n p m k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n)
    (hP : StrictMono P) (hQ : StrictMono Q) (hR : StrictMono R) (hC : StrictMono C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    {e s : ℝ} (hH : (M.submatrix P Q).det ≠ 0)
    (heH : 0 < e * (M.submatrix P Q).det)
    (hminor : HasSignedMinors M (p + k) s) :
    HasSignedMinors (signedSchurAt M P Q R C) k (e * s) := by
  intro rows cols hr hc
  obtain ⟨Rall, Call, hRall, hCall, _, _, hdet⟩ :=
    signedSchurAt_exists_sorted_det M P Q (R ∘ rows) (C ∘ cols)
      hP hQ (hR.comp hr) (hC.comp hc)
      (fun i j => hdisR i (rows j)) (fun i j => hdisC i (cols j)) hH
  have hm := hminor Rall Call hRall hCall
  have hratio : 0 ≤ e / (M.submatrix P Q).det := by
    rcases lt_or_gt_of_ne hH with hneg | hpos
    · apply div_nonneg_of_nonpos _ hneg.le
      nlinarith
    · apply div_nonneg _ hpos.le
      nlinarith
  rw [minor, signedSchurAt_submatrix, hdet]
  calc
    0 ≤ (s * minor M Rall Call) * (e / (M.submatrix P Q).det) := mul_nonneg hm hratio
    _ = _ := by ring

lemma signedSchurAt_nonsingular_complete {p m : ℕ} (M : Square (p + m))
    (P Q : Fin p → Fin (p + m)) (R C : Fin m → Fin (p + m))
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hR : Function.Injective R) (hC : Function.Injective C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (hM : M.det ≠ 0) (hH : (M.submatrix P Q).det ≠ 0) :
    (signedSchurAt M P Q R C).det ≠ 0 := by
  let er : Equiv.Perm (Fin (p + m)) := Equiv.ofBijective (appendIndices P R)
    ((Finite.injective_iff_bijective).mp (appendIndices_injective P R hP hR hdisR))
  let ec : Equiv.Perm (Fin (p + m)) := Equiv.ofBijective (appendIndices Q C)
    ((Finite.injective_iff_bijective).mp (appendIndices_injective Q C hQ hC hdisC))
  have hb : minor M (appendIndices P R) (appendIndices Q C) ≠ 0 := by
    intro hz
    have habs := Matrix.abs_det_submatrix_equiv_equiv er ec M
    change |minor M (appendIndices P R) (appendIndices Q C)| = |M.det| at habs
    rw [hz, abs_zero] at habs
    exact hM (abs_eq_zero.mp habs.symm)
  have hS := schurAt_nonsingular M P Q R C hH hb
  rw [signedSchurAt, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (pivotSign_diagonal_det_ne_zero P R) hS)
    (pivotSign_diagonal_det_ne_zero Q C)

noncomputable def scalarNormalizedSchur {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ : ℝ) : Square m :=
  (e * e₁) • signedSchurAt M P Q R C

lemma HasSignedMinors.smul {n k : ℕ} {M : Square n} {s a b : ℝ}
    (h : HasSignedMinors M k s) (hcoeff : b * a ^ k = s) :
    HasSignedMinors (a • M) k b := by
  intro rows cols hr hc
  have hm := h rows cols hr hc
  change 0 ≤ b * (a • M.submatrix rows cols).det
  rw [Matrix.det_smul, Fintype.card_fin, ← mul_assoc, hcoeff]
  exact hm

lemma HasSignedMinors.entries {n : ℕ} {M : Square n}
    (h : HasSignedMinors M 1 1) : NonnegativeEntries M := by
  intro i j
  have hc (x : Fin n) : StrictMono (fun _ : Fin 1 => x) := by
    intro a b hab
    exact False.elim ((ne_of_lt hab) (Subsingleton.elim _ _))
  simpa only [minor, Matrix.det_unique, Matrix.submatrix_apply, one_mul] using
    h (fun _ => i) (fun _ => j) (hc i) (hc j)

lemma HasSignedMinors.two {n : ℕ} {M : Square n} {s : ℝ}
    (h : HasSignedMinors M 2 s) (i j k l : Fin n) (hij : i < j) (hkl : k < l) :
    0 ≤ s * (M i k * M j l - M i l * M j k) := by
  have hr : StrictMono ![i, j] := strictMono_vecEmpty.vecCons hij
  have hc : StrictMono ![k, l] := strictMono_vecEmpty.vecCons hkl
  have hm := h ![i, j] ![k, l] hr hc
  rw [minor, Matrix.det_fin_two] at hm
  simpa using hm

lemma scalarNormalizedSchur_sign_one {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ : ℝ)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 1 (e * e₁)) :
    HasSignedMinors (scalarNormalizedSchur M P Q R C e e₁) 1 1 :=
  h.smul (by ring)

lemma scalarNormalizedSchur_sign_two {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (he : e = 1 ∨ e = -1) (he₁ : e₁ = 1 ∨ e₁ = -1)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 2 (e * e₂)) :
    HasSignedMinors (scalarNormalizedSchur M P Q R C e e₁) 2 (e * e₂) := by
  apply h.smul
  rcases he with rfl | rfl <;> rcases he₁ with rfl | rfl <;> ring

lemma scalarNormalizedSchur_sign_three {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₃ : ℝ)
    (he : e = 1 ∨ e = -1) (he₁ : e₁ = 1 ∨ e₁ = -1)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 3 (e * e₃)) :
    HasSignedMinors (scalarNormalizedSchur M P Q R C e e₁) 3 (e₁ * e₃) := by
  apply h.smul
  rcases he with rfl | rfl <;> rcases he₁ with rfl | rfl <;> ring

def reverseRows {n : ℕ} (M : Square n) : Square n := M.submatrix Fin.rev id

lemma reverseRows_nonsingular {n : ℕ} (M : Square n) (hM : M.det ≠ 0) :
    (reverseRows M).det ≠ 0 := by
  change (M.submatrix Fin.revPerm id).det ≠ 0
  rw [Matrix.det_permute]
  apply mul_ne_zero _ hM
  have hs := real_perm_sign_square (Fin.revPerm (n := n))
  intro hz
  rw [hz, zero_mul] at hs
  norm_num at hs

lemma reversedIncreasing {n k : ℕ} (rows : Fin k → Fin n) (hr : StrictMono rows) :
    StrictMono (fun i : Fin k => (rows i.rev).rev) := by
  intro i j hij
  apply Fin.rev_lt_rev.mpr
  exact hr (Fin.rev_lt_rev.mpr hij)

lemma reverseRows_minor_two {n : ℕ} (M : Square n) (rows cols : Fin 2 → Fin n) :
    minor (reverseRows M) rows cols = -minor M (fun i => (rows i.rev).rev) cols := by
  rw [minor, minor, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [reverseRows, Matrix.submatrix_apply, Fin.rev]
  ring

lemma reverseRows_minor_three {n : ℕ} (M : Square n) (rows cols : Fin 3 → Fin n) :
    minor (reverseRows M) rows cols = -minor M (fun i => (rows i.rev).rev) cols := by
  rw [minor, minor, Matrix.det_fin_three, Matrix.det_fin_three]
  simp [reverseRows, Matrix.submatrix_apply, Fin.rev]
  ring

lemma HasSignedMinors.reverseRows_two {n : ℕ} {M : Square n} {s : ℝ}
    (h : HasSignedMinors M 2 s) : HasSignedMinors (reverseRows M) 2 (-s) := by
  intro rows cols hr hc
  rw [reverseRows_minor_two, neg_mul_neg]
  exact h _ _ (reversedIncreasing rows hr) hc

lemma HasSignedMinors.reverseRows_three {n : ℕ} {M : Square n} {s : ℝ}
    (h : HasSignedMinors M 3 s) : HasSignedMinors (reverseRows M) 3 (-s) := by
  intro rows cols hr hc
  rw [reverseRows_minor_three, neg_mul_neg]
  exact h _ _ (reversedIncreasing rows hr) hc

noncomputable def normalizedSchur {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ) : Square m := by
  classical
  exact if e * e₂ = 1 then scalarNormalizedSchur M P Q R C e e₁
    else reverseRows (scalarNormalizedSchur M P Q R C e e₁)

lemma sign_product {a b : ℝ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

lemma normalizedSchur_nonnegative {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 1 (e * e₁)) :
    NonnegativeEntries (normalizedSchur M P Q R C e e₁ e₂) := by
  have hn := (scalarNormalizedSchur_sign_one M P Q R C e e₁ h).entries
  unfold normalizedSchur
  split_ifs
  · exact hn
  · exact hn.submatrix Fin.rev id

lemma normalizedSchur_tp2 {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (he : e = 1 ∨ e = -1) (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 2 (e * e₂)) :
    TP2 (normalizedSchur M P Q R C e e₁ e₂) := by
  have hn := scalarNormalizedSchur_sign_two M P Q R C e e₁ e₂ he he₁ h
  unfold normalizedSchur
  split_ifs with hs
  · rw [hs] at hn
    intro i j k l hij hkl
    simpa only [one_mul] using hn.two i j k l hij hkl
  · have hsneg : e * e₂ = -1 := (sign_product he he₂).resolve_left hs
    have hr := hn.reverseRows_two
    rw [hsneg, neg_neg] at hr
    intro i j k l hij hkl
    simpa only [one_mul] using hr.two i j k l hij hkl

lemma normalizedSchur_three {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ e₃ : ℝ)
    (he : e = 1 ∨ e = -1) (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (h : HasSignedMinors (signedSchurAt M P Q R C) 3 (e * e₃)) :
    HasSignedMinors (normalizedSchur M P Q R C e e₁ e₂) 3 (e * e₁ * e₂ * e₃) := by
  have hn := scalarNormalizedSchur_sign_three M P Q R C e e₁ e₃ he he₁ h
  have heq : e * e₁ * e₂ * e₃ = (e * e₂) * (e₁ * e₃) := by ring
  rw [heq]
  unfold normalizedSchur
  split_ifs with hs
  · rwa [hs, one_mul]
  · have hsneg : e * e₂ = -1 := (sign_product he he₂).resolve_left hs
    rw [hsneg, neg_one_mul]
    exact hn.reverseRows_three

lemma scalarNormalizedSchur_nonsingular {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ : ℝ)
    (ha : e * e₁ ≠ 0) (hS : (signedSchurAt M P Q R C).det ≠ 0) :
    (scalarNormalizedSchur M P Q R C e e₁).det ≠ 0 := by
  rw [scalarNormalizedSchur, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ ha) hS

lemma normalizedSchur_nonsingular {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (ha : e * e₁ ≠ 0) (hS : (signedSchurAt M P Q R C).det ≠ 0) :
    (normalizedSchur M P Q R C e e₁ e₂).det ≠ 0 := by
  have hn := scalarNormalizedSchur_nonsingular M P Q R C e e₁ ha hS
  unfold normalizedSchur
  split_ifs
  · exact hn
  · exact reverseRows_nonsingular _ hn

noncomputable def orientedRows {m k : ℕ} (rows : Fin k → Fin m) (e e₂ : ℝ) :
    Fin k → Fin m := by
  classical
  exact if e * e₂ = 1 then rows else fun i => (rows i.rev).rev

lemma orientedRows_strictMono {m k : ℕ} (rows : Fin k → Fin m) (e e₂ : ℝ)
    (hr : StrictMono rows) : StrictMono (orientedRows rows e e₂) := by
  unfold orientedRows
  split_ifs
  · exact hr
  · exact reversedIncreasing rows hr

lemma normalizedSchur_submatrix {n p m r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m) :
    (normalizedSchur M P Q R C e e₁ e₂).submatrix (orientedRows rows e e₂) cols =
      if e * e₂ = 1 then
        (e * e₁) • signedSchurAt M P Q (R ∘ rows) (C ∘ cols)
      else ((e * e₁) • signedSchurAt M P Q (R ∘ rows) (C ∘ cols)).submatrix
        Fin.rev id := by
  classical
  unfold normalizedSchur orientedRows
  split_ifs <;> ext i j <;>
    simp only [scalarNormalizedSchur, reverseRows, Matrix.submatrix_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.rev_rev]
  · exact congrArg (fun N : Matrix (Fin r) (Fin c) ℝ => (e * e₁) * N i j)
      (signedSchurAt_submatrix M P Q R C rows cols)
  · exact congrArg (fun N : Matrix (Fin r) (Fin c) ℝ => (e * e₁) * N i.rev j)
      (signedSchurAt_submatrix M P Q R C rows cols)

/-- Rank lifting can use the selected rows in increasing order after
the global row reversal; the finite row reversal within the selected block
does not affect rank. -/
theorem normalizedSchur_submatrix_rank {n p m r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m) (ha : e * e₁ ≠ 0) :
    ((normalizedSchur M P Q R C e e₁ e₂).submatrix
      (orientedRows rows e e₂) cols).rank =
      (schurAt M P Q (R ∘ rows) (C ∘ cols)).rank := by
  rw [normalizedSchur_submatrix]
  split_ifs
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha), signedSchurAt_rank]
  · change (((e * e₁) • signedSchurAt M P Q (R ∘ rows) (C ∘ cols)).submatrix
      Fin.revPerm (Equiv.refl _)).rank = _
    rw [Matrix.rank_submatrix, Matrix.rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha), signedSchurAt_rank]

lemma det_reverse_three (Y : Square 3) : (Y.submatrix Fin.rev id).det = -Y.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp [Matrix.submatrix_apply, Fin.rev]
  ring

/-- Exact order-three sign correspondence, including the order reversal
of the selected rows. This identity transports a wrong-sign bordered minor
without assuming any order-three inequality for the matrix being transformed. -/
theorem normalizedSchur_signed_three_eq {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ e₃ : ℝ)
    (he : e = 1 ∨ e = -1) (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (rows cols : Fin 3 → Fin m) :
    (e * e₁ * e₂ * e₃) * minor (normalizedSchur M P Q R C e e₁ e₂)
      (orientedRows rows e e₂) cols =
      (e * e₃) * minor (signedSchurAt M P Q R C) rows cols := by
  unfold minor
  rw [normalizedSchur_submatrix, signedSchurAt_submatrix]
  rcases he with rfl | rfl <;> rcases he₁ with rfl | rfl <;>
    rcases he₂ with rfl | rfl <;>
    norm_num [det_reverse_three, Matrix.det_smul, Matrix.det_neg]

/-- Lower-order closure uses only the two stated source orders. -/
theorem normalizedSchur_lower_closure {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n)
    (hP : StrictMono P) (hQ : StrictMono Q) (hR : StrictMono R) (hC : StrictMono C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (e e₁ e₂ : ℝ) (he : e = 1 ∨ e = -1)
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (hH : (M.submatrix P Q).det ≠ 0) (heH : 0 < e * (M.submatrix P Q).det)
    (h₁ : HasSignedMinors M (p + 1) e₁) (h₂ : HasSignedMinors M (p + 2) e₂) :
    NonnegativeEntries (normalizedSchur M P Q R C e e₁ e₂) ∧
      TP2 (normalizedSchur M P Q R C e e₁ e₂) := by
  refine ⟨normalizedSchur_nonnegative M P Q R C e e₁ e₂ ?_,
    normalizedSchur_tp2 M P Q R C e e₁ e₂ he he₁ he₂ ?_⟩
  · exact signedSchurAt_inherits_sign M P Q R C hP hQ hR hC hdisR hdisC hH heH h₁
  · exact signedSchurAt_inherits_sign M P Q R C hP hQ hR hC hdisR hdisC hH heH h₂

/-- Third-order closure is separate from lower-order closure. It is used
at endpoints, and never inferred from the lower-order assumptions at an
interior matrix. -/
theorem normalizedSchur_third_closure {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n)
    (hP : StrictMono P) (hQ : StrictMono Q) (hR : StrictMono R) (hC : StrictMono C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (e e₁ e₂ e₃ : ℝ) (he : e = 1 ∨ e = -1)
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (hH : (M.submatrix P Q).det ≠ 0) (heH : 0 < e * (M.submatrix P Q).det)
    (h₃ : HasSignedMinors M (p + 3) e₃) :
    HasSignedMinors (normalizedSchur M P Q R C e e₁ e₂) 3 (e * e₁ * e₂ * e₃) := by
  apply normalizedSchur_three M P Q R C e e₁ e₂ e₃ he he₁ he₂
  exact signedSchurAt_inherits_sign M P Q R C hP hQ hR hC hdisR hdisC hH heH h₃

theorem normalizedSchur_nonsingular_complete {p m : ℕ} (M : Square (p + m))
    (P Q : Fin p → Fin (p + m)) (R C : Fin m → Fin (p + m))
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hR : Function.Injective R) (hC : Function.Injective C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (e e₁ e₂ : ℝ) (ha : e * e₁ ≠ 0)
    (hM : M.det ≠ 0) (hH : (M.submatrix P Q).det ≠ 0) :
    (normalizedSchur M P Q R C e e₁ e₂).det ≠ 0 := by
  apply normalizedSchur_nonsingular M P Q R C e e₁ e₂ ha
  exact signedSchurAt_nonsingular_complete M P Q R C hP hQ hR hC hdisR hdisC hM hH

def pivotSignature (ε : ℕ → ℝ) (p : ℕ) : ℝ := if p = 0 then 1 else ε p

lemma pivotSignature_sign {n p : ℕ} {ε : ℕ → ℝ} (hε : IsSignature n ε) (hp : p ≤ n) :
    pivotSignature ε p = 1 ∨ pivotSignature ε p = -1 := by
  unfold pivotSignature
  split_ifs with hp0
  · exact Or.inl rfl
  · exact hε p (by omega) hp

lemma pivotSignature_mul_det_pos {n p : ℕ} {ε : ℕ → ℝ} (M : Square n)
    (P Q : Fin p → Fin n) (hP : StrictMono P) (hQ : StrictMono Q)
    (hε : IsSignature n ε) (hM : SignRegular ε M)
    (hH : (M.submatrix P Q).det ≠ 0) :
    0 < pivotSignature ε p * (M.submatrix P Q).det := by
  by_cases hp0 : p = 0
  · subst p
    simp [pivotSignature]
  · have hpn : p ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P hP.injective
    have hsign := hε p (by omega) hpn
    have hm := hM p (by omega) hpn P Q hP hQ
    have hne : ε p * (M.submatrix P Q).det ≠ 0 := by
      apply mul_ne_zero _ hH
      rcases hsign with h | h <;> simp [h]
    simpa only [pivotSignature, ite_eq_right hp0, minor] using
      lt_of_le_of_ne hm (Ne.symm hne)

lemma SignRegular.hasSignedMinors {n k : ℕ} {ε : ℕ → ℝ} {M : Square n}
    (h : SignRegular ε M) (hk : 1 ≤ k) (hkn : k ≤ n) :
    HasSignedMinors M k (ε k) := h k hk hkn

lemma pivot_ratio_pos {e d : ℝ} (hd : d ≠ 0) (hed : 0 < e * d) : 0 < e / d := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · apply div_pos_of_neg_of_neg _ hneg
    nlinarith
  · apply div_pos _ hpos
    nlinarith

/-- A wrong-sign bordered three-minor becomes a wrong-sign minor of the
normalized Schur matrix. No third-order source sign assumption occurs. -/
theorem normalizedSchur_wrong_three {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n)
    (hP : StrictMono P) (hQ : StrictMono Q) (hR : StrictMono R) (hC : StrictMono C)
    (e e₁ e₂ e₃ : ℝ) (he : e = 1 ∨ e = -1)
    (he₁ : e₁ = 1 ∨ e₁ = -1) (he₂ : e₂ = 1 ∨ e₂ = -1)
    (rows cols : Fin 3 → Fin m) (hr : StrictMono rows) (hc : StrictMono cols)
    (Rall Call : Fin (p + 3) → Fin n)
    (σ τ : Equiv.Perm (Fin (p + 3)))
    (hRall : StrictMono Rall) (hCall : StrictMono Call)
    (hsortR : appendIndices P (R ∘ rows) = Rall ∘ σ)
    (hsortC : appendIndices Q (C ∘ cols) = Call ∘ τ)
    (hH : (M.submatrix P Q).det ≠ 0) (heH : 0 < e * (M.submatrix P Q).det)
    (hbad : e₃ * minor M Rall Call < 0) :
    (e * e₁ * e₂ * e₃) * minor (normalizedSchur M P Q R C e e₁ e₂)
      (orientedRows rows e e₂) cols < 0 := by
  rw [normalizedSchur_signed_three_eq M P Q R C e e₁ e₂ e₃ he he₁ he₂ rows cols,
    minor, signedSchurAt_submatrix,
    signedSchurAt_sorted_det M P Q (R ∘ rows) (C ∘ cols) Rall Call σ τ
      hP hQ (hR.comp hr) (hC.comp hc) hRall hCall hsortR hsortC hH]
  calc
    _ = (e / (M.submatrix P Q).det) * (e₃ * minor M Rall Call) := by ring
    _ < 0 := mul_neg_of_pos_of_neg (pivot_ratio_pos hH heH) hbad

end IV01
