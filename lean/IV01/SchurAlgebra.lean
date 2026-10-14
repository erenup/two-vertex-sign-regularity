import IV01.Definitions
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
# Schur determinant algebra

All pivot and residual index maps are explicit. Empty pivots are included.
The sorted-border formula below records the exact row and column sorting
permutations, rather than assuming their signs away.
-/

namespace IV01

open Matrix
open scoped BigOperators

def appendIndices {n p k : ℕ} (P : Fin p → Fin n) (R : Fin k → Fin n) :
    Fin (p + k) → Fin n :=
  fun i => Sum.elim P R (finSumFinEquiv.symm i)

noncomputable def schurAt {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n) :
    Matrix (Fin r) (Fin c) ℝ :=
  M.submatrix R C - M.submatrix R Q * (M.submatrix P Q)⁻¹ * M.submatrix P C

lemma appended_submatrix_as_blocks {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n) :
    (M.submatrix (appendIndices P R) (appendIndices Q C)).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix P Q) (M.submatrix P C)
        (M.submatrix R Q) (M.submatrix R C) := by
  ext i j
  cases i <;> cases j <;>
    simp [appendIndices, Matrix.submatrix_apply, Matrix.fromBlocks]

/-- The bordered determinant formula with the pivot indices listed first. -/
theorem schurAt_det_mul {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0) :
    minor M (appendIndices P R) (appendIndices Q C) =
      (M.submatrix P Q).det * (schurAt M P Q R C).det := by
  let := Matrix.invertibleOfIsUnitDet (M.submatrix P Q) (isUnit_iff_ne_zero.mpr hH)
  rw [minor, ← Matrix.det_submatrix_equiv_self finSumFinEquiv,
    appended_submatrix_as_blocks, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv]
  rfl

theorem schurAt_det_eq_div {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0) :
    (schurAt M P Q R C).det =
      minor M (appendIndices P R) (appendIndices Q C) / (M.submatrix P Q).det := by
  apply (eq_div_iff hH).mpr
  rw [schurAt_det_mul M P Q R C hH]
  ring

lemma minor_permuted {n k : ℕ} (M : Square n) (R C : Fin k → Fin n)
    (σ τ : Equiv.Perm (Fin k)) :
    minor M (R ∘ σ) (C ∘ τ) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) * minor M R C := by
  change (((M.submatrix R C).submatrix id τ).submatrix σ id).det = _
  rw [Matrix.det_permute, Matrix.det_permute']
  dsimp [minor]
  ring

lemma real_perm_sign_square {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
  norm_cast
  simp

/-- Sorting a bordered minor inserts exactly the two permutation signs.
The maps `Rall` and `Call` may be chosen as the increasing maps of the union
sets, and `σ`, `τ` are the permutations which list the pivot indices first. -/
theorem schurAt_sorted_det {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (Rall Call : Fin (p + k) → Fin n)
    (σ τ : Equiv.Perm (Fin (p + k)))
    (hR : appendIndices P R = Rall ∘ σ)
    (hC : appendIndices Q C = Call ∘ τ)
    (hH : (M.submatrix P Q).det ≠ 0) :
    (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
      (schurAt M P Q R C).det = minor M Rall Call / (M.submatrix P Q).det := by
  have hf := schurAt_det_mul M P Q R C hH
  rw [hR, hC, minor_permuted] at hf
  apply (eq_div_iff hH).mpr
  calc
    _ = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
      ((M.submatrix P Q).det * (schurAt M P Q R C).det) := by ring
    _ = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ)) *
      (((Equiv.Perm.sign τ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ)) *
        minor M Rall Call := by rw [← hf]; ring
    _ = minor M Rall Call := by rw [real_perm_sign_square, real_perm_sign_square]; ring

/-- A nonzero full bordered determinant implies a nonzero Schur determinant. -/
theorem schurAt_nonsingular {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0)
    (hM : minor M (appendIndices P R) (appendIndices Q C) ≠ 0) :
    (schurAt M P Q R C).det ≠ 0 := by
  rw [schurAt_det_mul M P Q R C hH] at hM
  exact (mul_ne_zero_iff.mp hM).2

lemma real_perm_sign_inversions {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) =
      ∏ i, ∏ j, (if i < j then if σ i < σ j then (1 : ℝ) else -1 else 1) := by
  have h := congrArg (fun u : ℤˣ => ((u : ℤ) : ℝ)) σ.sign_eq_prod_prod_Ioi
  simp only [Units.coe_prod, Int.cast_prod, apply_ite, Units.val_one,
    Units.val_neg, Int.cast_one, Int.cast_neg] at h
  rw [h]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

/-- The sign of an order-preserving two-block shuffle is the product of
its cross-block inversion signs. -/
lemma real_perm_sign_shuffle {p k : ℕ} (σ : Equiv.Perm (Fin (p + k)))
    (hP : StrictMono (fun i : Fin p => σ (Fin.castAdd k i)))
    (hR : StrictMono (fun i : Fin k => σ (Fin.natAdd p i))) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) =
      ∏ j : Fin k, ∏ i : Fin p,
        (if σ (Fin.castAdd k i) < σ (Fin.natAdd p j) then (1 : ℝ) else -1) := by
  have hPP (i j : Fin p) :
      (if Fin.castAdd k i < Fin.castAdd k j then
        if σ (Fin.castAdd k i) < σ (Fin.castAdd k j) then (1 : ℝ) else -1 else 1) = 1 := by
    by_cases h : i < j
    · simp [show Fin.castAdd k i < Fin.castAdd k j from h, hP h]
    · simp [show ¬Fin.castAdd k i < Fin.castAdd k j from h]
  have hRR (i j : Fin k) :
      (if Fin.natAdd p i < Fin.natAdd p j then
        if σ (Fin.natAdd p i) < σ (Fin.natAdd p j) then (1 : ℝ) else -1 else 1) = 1 := by
    by_cases h : i < j
    · simp [Fin.natAdd_lt_natAdd_iff, h, hR h]
    · simp [Fin.natAdd_lt_natAdd_iff, h]
  have hPR (i : Fin p) (j : Fin k) : Fin.castAdd k i < Fin.natAdd p j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hRP (i : Fin k) (j : Fin p) : ¬Fin.natAdd p i < Fin.castAdd k j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  rw [real_perm_sign_inversions]
  simp_rw [Fin.prod_univ_add (a := p) (b := k), hPP, hRR,
    ite_eq_left (hPR _ _), ite_eq_right (hRP _ _)]
  simp only [Finset.prod_const_one, one_mul, mul_one]
  exact Finset.prod_comm

/-- The insertion sign contributed by a residual index, counted against
the strictly increasing pivot index map. -/
def pivotSign {n p : ℕ} (P : Fin p → Fin n) (r : Fin n) : ℝ :=
  (-1 : ℝ) ^ ((Finset.univ.filter fun i => r < P i).card)

lemma pivotSign_eq_product {n p : ℕ} (P : Fin p → Fin n) (r : Fin n)
    (hdis : ∀ i, P i ≠ r) :
    pivotSign P r = ∏ i, (if P i < r then (1 : ℝ) else -1) := by
  have hpoint (i : Fin p) :
      (if P i < r then (1 : ℝ) else -1) = (if r < P i then -1 else 1) := by
    rcases lt_or_gt_of_ne (hdis i) with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  simp_rw [hpoint]
  rw [← Finset.prod_filter]
  simp [pivotSign]

@[simp] lemma appendIndices_left {n p k : ℕ}
    (P : Fin p → Fin n) (R : Fin k → Fin n) (i : Fin p) :
    appendIndices P R (Fin.castAdd k i) = P i := by
  simp [appendIndices]

@[simp] lemma appendIndices_right {n p k : ℕ}
    (P : Fin p → Fin n) (R : Fin k → Fin n) (i : Fin k) :
    appendIndices P R (Fin.natAdd p i) = R i := by
  simp [appendIndices]

/-- For increasing pivot and residual maps, the sorting permutation has
the product of the per-index insertion signs stated in the paper. -/
theorem sorting_sign_eq_pivotSigns {n p k : ℕ}
    (P : Fin p → Fin n) (R : Fin k → Fin n) (All : Fin (p + k) → Fin n)
    (σ : Equiv.Perm (Fin (p + k)))
    (hP : StrictMono P) (hR : StrictMono R) (hAll : StrictMono All)
    (hsort : appendIndices P R = All ∘ σ) :
    ((Equiv.Perm.sign σ : ℤ) : ℝ) = ∏ j, pivotSign P (R j) := by
  have eP (i : Fin p) : All (σ (Fin.castAdd k i)) = P i := by
    simpa only [appendIndices_left, Function.comp_apply] using
      (congrFun hsort (Fin.castAdd k i)).symm
  have eR (j : Fin k) : All (σ (Fin.natAdd p j)) = R j := by
    simpa only [appendIndices_right, Function.comp_apply] using
      (congrFun hsort (Fin.natAdd p j)).symm
  have hPσ : StrictMono (fun i : Fin p => σ (Fin.castAdd k i)) := by
    intro i j hij
    apply hAll.lt_iff_lt.mp
    rw [eP, eP]
    exact hP hij
  have hRσ : StrictMono (fun j : Fin k => σ (Fin.natAdd p j)) := by
    intro i j hij
    apply hAll.lt_iff_lt.mp
    rw [eR, eR]
    exact hR hij
  have hdis (i : Fin p) (j : Fin k) : P i ≠ R j := by
    intro heq
    have heq' : Fin.castAdd k i = Fin.natAdd p j :=
      σ.injective (hAll.injective (by rw [eP, eR, heq]))
    have hv := congrArg Fin.val heq'
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  rw [real_perm_sign_shuffle σ hPσ hRσ]
  apply Finset.prod_congr rfl
  intro j _
  rw [pivotSign_eq_product P (R j) (fun i => hdis i j)]
  apply Finset.prod_congr rfl
  intro i _
  have hc : σ (Fin.castAdd k i) < σ (Fin.natAdd p j) ↔ P i < R j := by
    rw [← hAll.lt_iff_lt, eP, eR]
  simp only [hc]

noncomputable def signedSchurAt {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n) :
    Matrix (Fin r) (Fin c) ℝ :=
  Matrix.diagonal (fun i => pivotSign P (R i)) * schurAt M P Q R C *
    Matrix.diagonal (fun j => pivotSign Q (C j))

lemma signedSchurAt_det {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n) :
    (signedSchurAt M P Q R C).det =
      (∏ i, pivotSign P (R i)) * (∏ j, pivotSign Q (C j)) *
        (schurAt M P Q R C).det := by
  rw [signedSchurAt, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- Equation (4.1), with the increasing maps of the two union sets and
their sorting permutations supplied explicitly. All border sizes, including
zero, are allowed. There is no principal-pivot or consecutive-index hypothesis. -/
theorem signedSchurAt_sorted_det {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (Rall Call : Fin (p + k) → Fin n)
    (σ τ : Equiv.Perm (Fin (p + k)))
    (hP : StrictMono P) (hQ : StrictMono Q)
    (hR : StrictMono R) (hC : StrictMono C)
    (hRall : StrictMono Rall) (hCall : StrictMono Call)
    (hsortR : appendIndices P R = Rall ∘ σ)
    (hsortC : appendIndices Q C = Call ∘ τ)
    (hH : (M.submatrix P Q).det ≠ 0) :
    (signedSchurAt M P Q R C).det =
      minor M Rall Call / (M.submatrix P Q).det := by
  rw [signedSchurAt_det,
    ← sorting_sign_eq_pivotSigns P R Rall σ hP hR hRall hsortR,
    ← sorting_sign_eq_pivotSigns Q C Call τ hQ hC hCall hsortC]
  exact schurAt_sorted_det M P Q R C Rall Call σ τ hsortR hsortC hH

lemma exists_increasing_sort {n m : ℕ} (f : Fin m → Fin n)
    (hf : Function.Injective f) :
    ∃ (All : Fin m → Fin n) (σ : Equiv.Perm (Fin m)),
      StrictMono All ∧ f = All ∘ σ := by
  classical
  let s : Finset (Fin n) := Finset.univ.image f
  have hs : s.card = m := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective Finset.univ hf
  let e : Fin m ≃ s := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hf (congrArg Subtype.val h), by
      intro y
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp y.property
      exact ⟨i, Subtype.ext hi⟩⟩
  let o := s.orderIsoOfFin hs
  refine ⟨s.orderEmbOfFin hs, e.trans o.symm.toEquiv,
    (s.orderEmbOfFin hs).strictMono, ?_⟩
  funext i
  change f i = ↑(o (o.symm (e i)))
  simp only [OrderIso.apply_symm_apply]
  rfl

lemma appendIndices_injective {n p k : ℕ}
    (P : Fin p → Fin n) (R : Fin k → Fin n)
    (hP : Function.Injective P) (hR : Function.Injective R)
    (hdis : ∀ i j, P i ≠ R j) : Function.Injective (appendIndices P R) := by
  apply Function.Injective.comp _ finSumFinEquiv.symm.injective
  exact Sum.elim_injective.mpr ⟨hP, hR, hdis⟩

/-- Automatic sorted-union version of (4.1). The only index hypotheses
are strict monotonicity and disjointness of pivot and residual indices. -/
theorem signedSchurAt_exists_sorted_det {n p k : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin k → Fin n)
    (hP : StrictMono P) (hQ : StrictMono Q)
    (hR : StrictMono R) (hC : StrictMono C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (hH : (M.submatrix P Q).det ≠ 0) :
    ∃ Rall Call : Fin (p + k) → Fin n,
      StrictMono Rall ∧ StrictMono Call ∧
      Set.range Rall = Set.range (appendIndices P R) ∧
      Set.range Call = Set.range (appendIndices Q C) ∧
      (signedSchurAt M P Q R C).det =
        minor M Rall Call / (M.submatrix P Q).det := by
  obtain ⟨Rall, σ, hRall, hsortR⟩ := exists_increasing_sort (appendIndices P R)
    (appendIndices_injective P R hP.injective hR.injective hdisR)
  obtain ⟨Call, τ, hCall, hsortC⟩ := exists_increasing_sort (appendIndices Q C)
    (appendIndices_injective Q C hQ.injective hC.injective hdisC)
  refine ⟨Rall, Call, hRall, hCall, ?_, ?_,
    signedSchurAt_sorted_det M P Q R C Rall Call σ τ hP hQ hR hC
      hRall hCall hsortR hsortC hH⟩
  · rw [hsortR]
    exact (σ.surjective.range_comp Rall).symm
  · rw [hsortC]
    exact (τ.surjective.range_comp Call).symm

end IV01
