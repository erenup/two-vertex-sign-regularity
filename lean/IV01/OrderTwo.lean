import IV01.AdjacentTP2
import IV01.BoxContinuity

set_option backward.isDefEq.respectTransparency false

namespace IV01

def twoExpr {r c : Type*} (M : Matrix r c ℝ) (i j : r) (k l : c) : ℝ :=
  M i k * M j l - M i l * M j k

theorem SignRegular.two {n : ℕ} {ε : ℕ → ℝ} {M : Square n}
    (hM : SignRegular ε M) {i j k l : Fin n} (hij : i < j) (hkl : k < l) :
    0 ≤ ε 2 * twoExpr M i j k l := by
  have hn : 2 ≤ n := by have := j.isLt; omega
  have hr : StrictMono ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  have hc : StrictMono ![k, l] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  simpa [minor, Matrix.det_fin_two, twoExpr] using
    hM 2 (by omega) hn ![i, j] ![k, l] hr hc

theorem twoExpr_smul_sign {r c : Type*} (M : Matrix r c ℝ)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (i j : r) (k l : c) :
    twoExpr (s • M) i j k l = twoExpr M i j k l := by
  rcases hs with rfl | rfl <;> simp [twoExpr, Matrix.smul_apply] <;> ring

def rowReflection {n : ℕ} (M : Square n) : Square n := M.submatrix Fin.rev id

theorem rowReflection_det_ne_zero {n : ℕ} {M : Square n} (hM : M.det ≠ 0) :
    (rowReflection M).det ≠ 0 := by
  change (M.submatrix (Fin.revPerm : Equiv.Perm (Fin n)) id).det ≠ 0
  rw [Matrix.det_permute]
  exact mul_ne_zero (by simp) hM

theorem rowReflection_nonnegative {n : ℕ} {M : Square n} (hM : NonnegativeEntries M) :
    NonnegativeEntries (rowReflection M) := fun i j => hM i.rev j

theorem rowReflection_TP2_of_nonpos {n : ℕ} {M : Square n}
    (hM : ∀ i j k l, i < j → k < l → twoExpr M i j k l ≤ 0) :
    TP2 (rowReflection M) := by
  intro i j k l hij hkl
  have h := hM j.rev i.rev k l (Fin.rev_lt_rev.mpr hij) hkl
  dsimp [rowReflection, Matrix.submatrix, twoExpr] at *
  nlinarith

theorem rowReflection_adjacent_of_nonpos {n : ℕ} {M : Square n}
    (hM : ∀ (i j : Fin n) (hi : i.val + 1 < n) (hj : j.val + 1 < n),
      twoExpr M i ⟨i.val + 1, hi⟩ j ⟨j.val + 1, hj⟩ ≤ 0) :
    AdjacentTP2 (rowReflection M) := by
  intro i j hi hj
  let i' : Fin n := ⟨i.val + 1, hi⟩
  have hr : i'.rev.val + 1 < n := by
    dsimp [i']
    omega
  have heq : (⟨i'.rev.val + 1, hr⟩ : Fin n) = i.rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp [i']
    omega
  have h := hM i'.rev j hr hj
  rw [heq] at h
  change 0 ≤ twoExpr M i.rev i'.rev j ⟨j.val + 1, hj⟩
  dsimp [twoExpr] at *
  nlinarith

theorem scalar_support_of_interior {l u x s : ℝ}
    (hs : s = 1 ∨ s = -1) (hx : l ≤ x ∧ x ≤ u)
    (hint : l < u → l < x ∧ x < u) (hl : 0 ≤ s * l) (hu : 0 ≤ s * u) :
    0 < s * x ↔ 0 < s * l ∨ 0 < s * u := by
  by_cases heq : l = u
  · have hxl : x = l := by linarith
    simp [hxl, heq]
  · have hlu : l < u := lt_of_le_of_ne (hx.1.trans hx.2) heq
    have hxi := hint hlu
    rcases hs with rfl | rfl
    · simp only [one_mul] at *
      constructor
      · intro h
        exact Or.inr (lt_of_lt_of_le h hx.2)
      · intro _
        exact lt_of_le_of_lt hl hxi.1
    · simp only [neg_one_mul] at *
      constructor
      · intro h
        left
        linarith
      · intro _
        linarith

theorem scaled_checker_support {n : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hε : IsSignature n ε)
    (hminus : SignRegular ε (checkerMinus L U))
    (hplus : SignRegular ε (checkerPlus L U))
    (hM : InRelativeInterior L U M) (i j : Fin n) :
    0 < (ε 1 • M) i j ↔
      0 < (ε 1 • checkerMinus L U) i j ∨ 0 < (ε 1 • checkerPlus L U) i j := by
  have hn : 1 ≤ n := by have := i.isLt; omega
  have hm := hminus.entry i j
  have hp := hplus.entry i j
  have he := scalar_support_of_interior (hε 1 le_rfl hn)
    ⟨hM.1.1 i j, hM.1.2 i j⟩ (hM.2 i j)
  dsimp [checkerMinus, checkerPlus] at hm hp ⊢
  split_ifs at hm hp ⊢
  · exact he hm hp
  · simpa only [or_comm] using he hp hm

theorem signed_adjacent_in_box {n : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hLU : EntrywiseLE L U) (hε : IsSignature n ε)
    (hminus : SignRegular ε (checkerMinus L U))
    (hplus : SignRegular ε (checkerPlus L U)) (hM : InBox L U M)
    (i j : Fin n) (hi : i.val + 1 < n) (hj : j.val + 1 < n) :
    0 ≤ ε 2 * twoExpr M i ⟨i.val + 1, hi⟩ j ⟨j.val + 1, hj⟩ := by
  have ha : i.val + 2 ≤ n := by omega
  have hb : j.val + 2 ≤ n := by omega
  have h := solid_minor_sign (q := 0) hLU hε hminus hplus ha hb
    (fun X hX rows cols _ _ => by
      simpa [minor, Matrix.det_unique] using entry_sign_in_box hminus hplus hX (rows 0) (cols 0)) hM
  simpa [minor, Matrix.det_fin_two, Matrix.submatrix_apply, consecutiveIndices, twoExpr] using h

/-- The complete order-two interval result at relative-interior points. -/
theorem order_two_interior {n : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hLU : EntrywiseLE L U) (hε : IsSignature n ε)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (hM : InRelativeInterior L U M) {i j k l : Fin n} (hij : i < j) (hkl : k < l) :
    0 ≤ ε 2 * twoExpr M i j k l := by
  have hn : 2 ≤ n := by have := j.isLt; omega
  have hs₁ := hε 1 (by omega) (by omega)
  have hs₁ne : ε 1 ≠ 0 := signature_ne_zero hε (by omega) (by omega)
  let A := ε 1 • checkerMinus L U
  let B := ε 1 • checkerPlus L U
  let X := ε 1 • M
  have hA : NonnegativeEntries A := hminus.2.entry
  have hB : NonnegativeEntries B := hplus.2.entry
  have hX : NonnegativeEntries X := entry_sign_in_box hminus.2 hplus.2 hM.1
  have hAd : A.det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs₁ne) hminus.1
  have hBd : B.det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hs₁ne) hplus.1
  have hsupp : ∀ a b, 0 < X a b ↔ 0 < A a b ∨ 0 < B a b :=
    scaled_checker_support hε hminus.2 hplus.2 hM
  have hA₂ : ∀ a b c d, a < b → c < d → 0 ≤ ε 2 * twoExpr A a b c d := by
    intro a b c d hab hcd
    rw [twoExpr_smul_sign _ _ hs₁]
    exact hminus.2.two hab hcd
  have hB₂ : ∀ a b c d, a < b → c < d → 0 ≤ ε 2 * twoExpr B a b c d := by
    intro a b c d hab hcd
    rw [twoExpr_smul_sign _ _ hs₁]
    exact hplus.2.two hab hcd
  have hXadj : ∀ (a b : Fin n) (ha : a.val + 1 < n) (hb : b.val + 1 < n),
      0 ≤ ε 2 * twoExpr X a ⟨a.val + 1, ha⟩ b ⟨b.val + 1, hb⟩ := by
    intro a b ha hb
    rw [twoExpr_smul_sign _ _ hs₁]
    exact signed_adjacent_in_box hLU hε hminus.2 hplus.2 hM.1 a b ha hb
  rcases hε 2 (by norm_num) hn with hs₂ | hs₂
  · simp only [hs₂, one_mul] at hA₂ hB₂ hXadj ⊢
    have hTP := tp2_of_adjacent_of_crossing_rectangles hX hXadj
      (crossing_rectangles_of_union_support hA hA₂ hAd hB hB₂ hBd hX hsupp)
    have h := hTP i j k l hij hkl
    change 0 ≤ twoExpr X i j k l at h
    rwa [twoExpr_smul_sign _ _ hs₁] at h
  · simp only [hs₂, neg_one_mul, neg_nonneg] at hA₂ hB₂ hXadj
    have hAr := rowReflection_nonnegative hA
    have hBr := rowReflection_nonnegative hB
    have hXr := rowReflection_nonnegative hX
    have hA₂r := rowReflection_TP2_of_nonpos hA₂
    have hB₂r := rowReflection_TP2_of_nonpos hB₂
    have hXadjr := rowReflection_adjacent_of_nonpos hXadj
    have hsuppr : ∀ a b, 0 < rowReflection X a b ↔
        0 < rowReflection A a b ∨ 0 < rowReflection B a b := fun a b => hsupp a.rev b
    have hTP := tp2_of_adjacent_of_crossing_rectangles hXr hXadjr
      (crossing_rectangles_of_union_support hAr hA₂r (rowReflection_det_ne_zero hAd)
        hBr hB₂r (rowReflection_det_ne_zero hBd) hXr hsuppr)
    have h := hTP j.rev i.rev k l (Fin.rev_lt_rev.mpr hij) hkl
    change 0 ≤ twoExpr (rowReflection X) j.rev i.rev k l at h
    have heq : twoExpr (rowReflection X) j.rev i.rev k l = -twoExpr X i j k l := by
      simp [twoExpr, rowReflection, Matrix.submatrix_apply]
      ring
    rw [heq, twoExpr_smul_sign _ _ hs₁] at h
    simpa [hs₂] using h

/-- Order two holds throughout the closed box, including its boundary. -/
theorem order_two_in_box {n : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hLU : EntrywiseLE L U) (hε : IsSignature n ε)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (hM : InBox L U M) (rows cols : Fin 2 → Fin n)
    (hr : StrictMono rows) (hc : StrictMono cols) : 0 ≤ ε 2 * minor M rows cols := by
  apply signed_minor_nonneg_on_box hLU rows cols (ε 2) ?_ hM
  intro X hX
  have h := order_two_interior hLU hε hminus hplus hX
    (hr (by decide : (0 : Fin 2) < 1)) (hc (by decide : (0 : Fin 2) < 1))
  simpa [minor, Matrix.det_fin_two, twoExpr] using h

end IV01
