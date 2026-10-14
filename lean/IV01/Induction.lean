import IV01.MinimalBad
import IV01.OrderTwo
import IV01.SchurClosure

/-!
# The all-order induction, separated from its three rectangle exclusions

This module proves the complete generic assembly with explicit hypotheses for
the fixed, positive-third-sign, and negative-third-sign rectangle exclusions.
The three exclusion hypotheses are explicit theorem parameters.
-/

namespace IV01

open Matrix

/-- All prescribed minor signs through a specified order, throughout the box. -/
def LowerMinorSigns {n : ℕ} (ε : ℕ → ℝ) (L U : Square n) (k : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ k → ∀ X, InBox L U X →
    ∀ rows cols : Fin j → Fin n, StrictMono rows → StrictMono cols →
      0 ≤ ε j * minor X rows cols

theorem LowerMinorSigns.transpose {n k : ℕ} {ε : ℕ → ℝ} {L U : Square n}
    (h : LowerMinorSigns ε L U k) : LowerMinorSigns ε Lᵀ Uᵀ k := by
  intro j hj hjk X hX rows cols hr hc
  have hXT : InBox L U Xᵀ := by simpa only [Matrix.transpose_transpose] using hX.transpose
  simpa only [minor_transpose] using h j hj hjk Xᵀ hXT cols rows hc hr

/-- Third-order signature after a pivot of order `p`; the empty pivot has
signature one independently of the unprescribed value `ε 0`. -/
def schurThirdSign (ε : ℕ → ℝ) (p : ℕ) : ℝ :=
  pivotSignature ε p * ε (p + 1) * ε (p + 2) * ε (p + 3)

theorem schurThirdSign_sign {n p : ℕ} {ε : ℕ → ℝ}
    (hε : IsSignature n ε) (hpn : p + 3 ≤ n) :
    schurThirdSign ε p = 1 ∨ schurThirdSign ε p = -1 := by
  rcases pivotSignature_sign hε (by omega : p ≤ n) with h0 | h0 <;>
    rcases hε (p + 1) (by omega) (by omega) with h1 | h1 <;>
    rcases hε (p + 2) (by omega) (by omega) with h2 | h2 <;>
    rcases hε (p + 3) (by omega) hpn with h3 | h3 <;>
    simp [schurThirdSign, h0, h1, h2, h3]

def FixedInteriorRectangle {n p : ℕ} (L U : Square n)
    (rows cols : Fin (p + 3) → Fin n) : Prop :=
  ∀ i, ∀ c : InteriorColumns cols, L (rows i) c.val = U (rows i) c.val

/-- Contract for the fixed interior rectangle branch. -/
def FixedRectangleExcluded : Prop :=
  ∀ (n p : ℕ) (ε : ℕ → ℝ) (L U : Square n),
    p + 3 ≤ n → IsSignature n ε → EntrywiseLE L U →
    NonsingularSignRegular ε (checkerMinus L U) →
    NonsingularSignRegular ε (checkerPlus L U) →
    LowerMinorSigns ε L U (p + 2) →
    ∀ M, InRelativeInterior L U M →
    ∀ rows cols : Fin (p + 3) → Fin n, StrictMono rows → StrictMono cols →
      ε (p + 3) * minor M rows cols < 0 →
      p + 2 ≤ Fintype.card (InteriorColumns cols) →
      (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = p + 1 →
      (∀ X, InBox L U X →
        (X.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ p + 1) →
      FixedInteriorRectangle L U rows cols → False

/-- Contract for a nonfixed interior rectangle of specified Schur third-order sign. -/
def SignedNonfixedRectangleExcluded (δ : ℝ) : Prop :=
  ∀ (n p : ℕ) (ε : ℕ → ℝ) (L U : Square n),
    p + 3 ≤ n → IsSignature n ε → EntrywiseLE L U →
    NonsingularSignRegular ε (checkerMinus L U) →
    NonsingularSignRegular ε (checkerPlus L U) →
    LowerMinorSigns ε L U (p + 2) →
    ∀ M, InRelativeInterior L U M →
    ∀ rows cols : Fin (p + 3) → Fin n, StrictMono rows → StrictMono cols →
      ε (p + 3) * minor M rows cols < 0 →
      p + 2 ≤ Fintype.card (InteriorColumns cols) →
      (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = p + 1 →
      (∀ X, InBox L U X →
        (X.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ p + 1) →
      ¬FixedInteriorRectangle L U rows cols → schurThirdSign ε p = δ → False

/-- The three exclusion contracts exhaust every bad rectangle certificate. -/
theorem no_bad_rectangle_of_exclusions
    (hfixed : FixedRectangleExcluded)
    (hpositive : SignedNonfixedRectangleExcluded 1)
    (hnegative : SignedNonfixedRectangleExcluded (-1))
    {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hpn : p + 3 ≤ n) (hε : IsSignature n ε) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (hlower : LowerMinorSigns ε L U (p + 2)) (hM : InRelativeInterior L U M)
    (rows cols : Fin (p + 3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : ε (p + 3) * minor M rows cols < 0)
    (hcard : p + 2 ≤ Fintype.card (InteriorColumns cols))
    (hrank : (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = p + 1)
    (hbound : ∀ X, InBox L U X →
      (X.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ p + 1) : False := by
  classical
  by_cases hfix : FixedInteriorRectangle L U rows cols
  · exact hfixed n p ε L U hpn hε hLU hminus hplus hlower M hM rows cols hr hc
      hbad hcard hrank hbound hfix
  · rcases schurThirdSign_sign hε hpn with hpos | hneg
    · exact hpositive n p ε L U hpn hε hLU hminus hplus hlower M hM rows cols hr hc
        hbad hcard hrank hbound hfix hpos
    · exact hnegative n p ε L U hpn hε hLU hminus hplus hlower M hM rows cols hr hc
        hbad hcard hrank hbound hfix hneg

/-- The higher-order step, including boundary-to-interior movement and the
orientation of a gap into the column direction. -/
theorem next_order_sign_of_exclusions
    (hfixed : FixedRectangleExcluded)
    (hpositive : SignedNonfixedRectangleExcluded 1)
    (hnegative : SignedNonfixedRectangleExcluded (-1))
    {n p : ℕ} {ε : ℕ → ℝ} {L U : Square n}
    (hpn : p + 3 ≤ n) (hε : IsSignature n ε) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (hlower : LowerMinorSigns ε L U (p + 2))
    {X : Square n} (hX : InBox L U X)
    (rows cols : Fin (p + 3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols) :
    0 ≤ ε (p + 3) * minor X rows cols := by
  by_contra hneg
  obtain ⟨M, hM, hbad⟩ := exists_interior_bad_minor hLU rows cols (ε (p + 3)) hX (lt_of_not_ge hneg)
  have hη : ε (p + 2) ≠ 0 := signature_ne_zero hε (by omega) (by omega)
  have hlower' : ∀ Y, InBox L U Y → ∀ a b : Fin (p + 2) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ ε (p + 2) * minor Y a b :=
    fun Y hY a b ha hb => hlower (p + 2) (by omega) le_rfl Y hY a b ha hb
  have hsolid : ∀ (a b : ℕ) (ha : a + (p + 3) ≤ n) (hb : b + (p + 3) ≤ n),
      0 ≤ ε (p + 3) * minor M (consecutiveIndices n (p + 3) a ha)
        (consecutiveIndices n (p + 3) b hb) := by
    intro a b ha hb
    exact solid_minor_sign (q := p + 1) hLU hε hminus.2 hplus.2 ha hb hlower' hM.1
  have hcert := exists_permanent_bad_rectangle_or_transpose (q := p + 1)
    (ε (p + 3)) (ε (p + 2)) hη hM hlower' hsolid ⟨rows, cols, hr, hc, hbad⟩
  rcases hcert with ⟨r, c, hr, hc, hb, hcard, hrank, hbound⟩ |
    ⟨r, c, hr, hc, hb, hcard, hrank, hbound⟩
  · exact no_bad_rectangle_of_exclusions hfixed hpositive hnegative hpn hε hLU hminus hplus
      hlower hM r c hr hc hb hcard hrank hbound
  · have hminusT : NonsingularSignRegular ε (checkerMinus Lᵀ Uᵀ) := by
      rw [checkerMinus_transpose]
      exact hminus.transpose
    have hplusT : NonsingularSignRegular ε (checkerPlus Lᵀ Uᵀ) := by
      rw [checkerPlus_transpose]
      exact hplus.transpose
    exact no_bad_rectangle_of_exclusions hfixed hpositive hnegative hpn hε hLU.transpose
      hminusT hplusT hlower.transpose hM.transpose r c hr hc hb hcard hrank hbound

/-- All minor signs follow by strong induction once the three rectangle
exclusions have been supplied. The induction includes every order and dimension. -/
theorem signRegular_of_rectangle_exclusions
    (hfixed : FixedRectangleExcluded)
    (hpositive : SignedNonfixedRectangleExcluded 1)
    (hnegative : SignedNonfixedRectangleExcluded (-1))
    {n : ℕ} {ε : ℕ → ℝ} {L U : Square n}
    (hε : IsSignature n ε) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    {X : Square n} (hX : InBox L U X) : SignRegular ε X := by
  have allOrders : ∀ k, 1 ≤ k → k ≤ n → ∀ Y, InBox L U Y →
      ∀ rows cols : Fin k → Fin n, StrictMono rows → StrictMono cols →
        0 ≤ ε k * minor Y rows cols := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkn Y hY rows cols hr hc
      by_cases hk1 : k = 1
      · subst k
        simpa only [minor, Matrix.det_unique, Matrix.submatrix_apply] using
          entry_sign_in_box hminus.2 hplus.2 hY (rows default) (cols default)
      by_cases hk2 : k = 2
      · subst k
        exact order_two_in_box hLU hε hminus hplus hY rows cols hr hc
      have hk3 : 3 ≤ k := by omega
      obtain ⟨p, rfl⟩ : ∃ p, k = p + 3 := ⟨k - 3, by omega⟩
      have hlower : LowerMinorSigns ε L U (p + 2) := by
        intro j hj hjp Z hZ a b ha hb
        exact ih j (by omega) hj (by omega) Z hZ a b ha hb
      exact next_order_sign_of_exclusions hfixed hpositive hnegative hkn hε hLU hminus hplus
        hlower hY rows cols hr hc
  intro k hk hkn rows cols hr hc
  exact allOrders k hk hkn X hX rows cols hr hc

/-- Complete interval conclusion, conditional only on the three explicit
rectangle exclusion theorems. -/
theorem nonsingularSignRegular_of_rectangle_exclusions
    (hfixed : FixedRectangleExcluded)
    (hpositive : SignedNonfixedRectangleExcluded 1)
    (hnegative : SignedNonfixedRectangleExcluded (-1))
    {n : ℕ} {ε : ℕ → ℝ} {L U : Square n}
    (hε : IsSignature n ε) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    {X : Square n} (hX : InBox L U X) : NonsingularSignRegular ε X :=
  ⟨inBox_nonsingular hε hminus hplus hX,
    signRegular_of_rectangle_exclusions hfixed hpositive hnegative hε hLU hminus hplus hX⟩

end IV01
