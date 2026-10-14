import IV01.TP2
import IV01.SolidMinors

set_option backward.isDefEq.respectTransparency false

namespace IV01

def AdjacentTP2 {r c : ℕ} (Y : Matrix (Fin r) (Fin c) ℝ) : Prop :=
  ∀ (i : Fin r) (j : Fin c) (hi : i.val + 1 < r) (hj : j.val + 1 < c),
    0 ≤ Y i j * Y ⟨i.val + 1, hi⟩ ⟨j.val + 1, hj⟩ -
      Y i ⟨j.val + 1, hj⟩ * Y ⟨i.val + 1, hi⟩ j

theorem tp2_of_positive_of_adjacent {r c : ℕ}
    {Y : Matrix (Fin (r + 1)) (Fin (c + 1)) ℝ}
    (hpos : ∀ i j, 0 < Y i j) (hadj : AdjacentTP2 Y) : TP2 Y := by
  have hrows : ∀ i : Fin r, ∀ k l : Fin (c + 1), k ≤ l →
      Y i.castSucc k * Y i.succ l - Y i.castSucc l * Y i.succ k ≥ 0 := by
    intro i k l hkl
    have hmono : Monotone (fun j : Fin (c + 1) => Y i.succ j / Y i.castSucc j) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j
      apply (div_le_div_iff₀ (hpos _ _) (hpos _ _)).mpr
      have h := hadj i.castSucc j.castSucc i.succ.isLt j.succ.isLt
      change 0 ≤ Y i.castSucc j.castSucc * Y i.succ j.succ -
        Y i.castSucc j.succ * Y i.succ j.castSucc at h
      nlinarith
    have h := (div_le_div_iff₀ (hpos _ _) (hpos _ _)).mp (hmono hkl)
    nlinarith
  intro i j k l hij hkl
  have hmono : Monotone (fun a : Fin (r + 1) => Y a l / Y a k) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro a
    apply (div_le_div_iff₀ (hpos _ _) (hpos _ _)).mpr
    have h := hrows a k l hkl.le
    nlinarith
  have h := (div_le_div_iff₀ (hpos _ _) (hpos _ _)).mp (hmono hij.le)
  nlinarith

theorem AdjacentTP2.submatrix_consecutive {m n p q a b : ℕ}
    {Y : Matrix (Fin m) (Fin n) ℝ} (hY : AdjacentTP2 Y)
    (ha : a + p ≤ m) (hb : b + q ≤ n) :
    AdjacentTP2 (Y.submatrix (consecutiveIndices m p a ha) (consecutiveIndices n q b hb)) := by
  intro i j hi hj
  have hir : (consecutiveIndices m p a ha i).val + 1 < m := by
    dsimp [consecutiveIndices]
    omega
  have hjc : (consecutiveIndices n q b hb j).val + 1 < n := by
    dsimp [consecutiveIndices]
    omega
  convert hY (consecutiveIndices m p a ha i) (consecutiveIndices n q b hb j) hir hjc using 1 <;>
    simp [Matrix.submatrix_apply, consecutiveIndices, Nat.add_assoc]

/-- Staircase support plus adjacent order-two signs imply all order-two signs.
The support condition only asks that the rectangle between positive crossing
entries be positive. -/
theorem tp2_of_adjacent_of_crossing_rectangles {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (hadj : AdjacentTP2 Y)
    (hrect : ∀ i j k l, i < j → k < l → 0 < Y i l → 0 < Y j k →
      ∀ r c, i ≤ r → r ≤ j → k ≤ c → c ≤ l → 0 < Y r c) : TP2 Y := by
  intro i j k l hij hkl
  by_cases hil : 0 < Y i l
  · by_cases hjk : 0 < Y j k
    · let p := j.val - i.val
      let q := l.val - k.val
      have hp : i.val + (p + 1) ≤ n := by have := j.isLt; dsimp [p]; omega
      have hq : k.val + (q + 1) ≤ n := by have := l.isLt; dsimp [q]; omega
      let rows := consecutiveIndices n (p + 1) i.val hp
      let cols := consecutiveIndices n (q + 1) k.val hq
      let B := Y.submatrix rows cols
      have hpos : ∀ a b, 0 < B a b := by
        intro a b
        apply hrect i j k l hij hkl hil hjk (rows a) (cols b)
        · change i.val ≤ i.val + a.val
          omega
        · change i.val + a.val ≤ j.val
          have := a.isLt
          dsimp [p] at this
          omega
        · change k.val ≤ k.val + b.val
          omega
        · change k.val + b.val ≤ l.val
          have := b.isLt
          dsimp [q] at this
          omega
      have hB := tp2_of_positive_of_adjacent hpos (hadj.submatrix_consecutive hp hq)
      have hr₀ : rows 0 = i := by apply Fin.ext; simp [rows, consecutiveIndices]
      have hr₁ : rows (Fin.last p) = j := by
        apply Fin.ext
        dsimp [rows, consecutiveIndices, p]
        omega
      have hc₀ : cols 0 = k := by apply Fin.ext; simp [cols, consecutiveIndices]
      have hc₁ : cols (Fin.last q) = l := by
        apply Fin.ext
        dsimp [cols, consecutiveIndices, q]
        omega
      have h₀₁ : (0 : Fin (p + 1)) < Fin.last p := by
        change 0 < p
        dsimp [p]
        omega
      have h₂₃ : (0 : Fin (q + 1)) < Fin.last q := by
        change 0 < q
        dsimp [q]
        omega
      have h := hB 0 (Fin.last p) 0 (Fin.last q) h₀₁ h₂₃
      simpa only [B, Matrix.submatrix_apply, hr₀, hr₁, hc₀, hc₁] using h
    · have hz : Y j k = 0 := le_antisymm (le_of_not_gt hjk) (hY j k)
      rw [hz, mul_zero, sub_zero]
      exact mul_nonneg (hY i k) (hY j l)
  · have hz : Y i l = 0 := le_antisymm (le_of_not_gt hil) (hY i l)
    rw [hz, zero_mul, sub_zero]
    exact mul_nonneg (hY i k) (hY j l)

/-- The union of two nonsingular nonnegative TP2 supports has the
crossing-rectangle property. -/
theorem crossing_rectangles_of_union_support {n : ℕ} {A B X : Square n}
    (hA : NonnegativeEntries A) (hA₂ : TP2 A) (hAd : A.det ≠ 0)
    (hB : NonnegativeEntries B) (hB₂ : TP2 B) (hBd : B.det ≠ 0)
    (hX : NonnegativeEntries X)
    (hsupport : ∀ i j, 0 < X i j ↔ 0 < A i j ∨ 0 < B i j) :
    ∀ i j k l, i < j → k < l → 0 < X i l → 0 < X j k →
      ∀ r c, i ≤ r → r ≤ j → k ≤ c → c ≤ l → 0 < X r c := by
  have hAdiag := diagonal_pos_of_nonsingular hA hA₂ hAd
  have hBdiag := diagonal_pos_of_nonsingular hB hB₂ hBd
  intro i j k l hij hkl hil hjk r c hir hrj hkc hcl
  by_contra hrc
  have ha : A r c = 0 := by
    apply le_antisymm _ (hA r c)
    by_contra! h
    exact hrc ((hsupport r c).mpr (Or.inl h))
  have hb : B r c = 0 := by
    apply le_antisymm _ (hB r c)
    by_contra! h
    exact hrc ((hsupport r c).mpr (Or.inr h))
  rcases lt_trichotomy r c with hlt | heq | hgt
  · have haz := northeast_zero hA hA₂ hAdiag hlt ha hir hcl
    have hbz := northeast_zero hB hB₂ hBdiag hlt hb hir hcl
    rcases (hsupport i l).mp hil with h | h <;> linarith
  · subst c
    have := hAdiag r
    linarith
  · have haz := southwest_zero hA hA₂ hAdiag hgt ha hrj hkc
    have hbz := southwest_zero hB hB₂ hBdiag hgt hb hrj hkc
    rcases (hsupport j k).mp hjk with h | h <;> linarith

end IV01
