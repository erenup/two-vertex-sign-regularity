import IV01.TP2
import Mathlib.Order.Fin.Tuple
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Zero restrictions for negative order-three sign

The first structural lemma proved here is Section 3.2 of the written proof.
All hypotheses are weak minor inequalities; nonsingularity supplies the
strict inequalities used in the argument.
-/

namespace IV01

def NonpositiveThreeMinors {ι κ : Type*} [Preorder ι] [Preorder κ]
    (Y : Matrix ι κ ℝ) : Prop :=
  ∀ rows : Fin 3 → ι, ∀ cols : Fin 3 → κ,
    StrictMono rows → StrictMono cols →
    Matrix.det (Y.submatrix rows cols) ≤ 0

theorem NonpositiveThreeMinors.transpose {ι κ : Type*}
    [Preorder ι] [Preorder κ] {Y : Matrix ι κ ℝ}
    (h₃ : NonpositiveThreeMinors Y) : NonpositiveThreeMinors Y.transpose := by
  intro rows cols hr hc
  change Matrix.det (Y.submatrix cols rows).transpose ≤ 0
  rw [Matrix.det_transpose]
  exact h₃ cols rows hc hr

/-- Any two distinct ordered columns of a nonsingular nonnegative TP2
matrix support a positive two-minor on some ordered pair of rows. -/
theorem exists_positive_two_minor_on_cols {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    {k l : Fin n} (hkl : k < l) :
    ∃ r s, r < s ∧ 0 < Y r k * Y s l - Y r l * Y s k := by
  classical
  by_contra hex
  have hz (r s : Fin n) (hrs : r < s) :
      Y r k * Y s l - Y r l * Y s k = 0 := by
    apply le_antisymm
    · exact le_of_not_gt (fun h => hex ⟨r, s, hrs, h⟩)
    · exact h₂ r s k l hrs hkl
  have hdiag := diagonal_pos_of_nonsingular hY h₂ hdet
  have heq : Y k k • Y.col l = Y k l • Y.col k := by
    ext r
    change Y k k * Y r l = Y k l * Y r k
    rcases lt_trichotomy k r with hkr | hkr | hrk
    · have := hz k r hkr
      linarith
    · subst r
      ring
    · have := hz r k hrk
      nlinarith
  have heqidx := (Matrix.linearIndependent_cols_of_det_ne_zero hdet).eq_of_smul_apply_eq_smul_apply
    (Y k k) (Y k l) l k (ne_of_gt (hdiag k)) heq
  exact hkl.ne heqidx.symm

/-- The transposed version fixes the two rows. -/
theorem exists_positive_two_minor_on_rows {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    {r s : Fin n} (hrs : r < s) :
    ∃ k l, k < l ∧ 0 < Y r k * Y s l - Y r l * Y s k := by
  obtain ⟨k, l, hkl, hpos⟩ := exists_positive_two_minor_on_cols
    hY.transpose h₂.transpose (by simpa only [Matrix.det_transpose] using hdet) hrs
  refine ⟨k, l, hkl, ?_⟩
  simpa only [Matrix.transpose_apply, mul_comm] using hpos

private theorem strictMono_three {ι : Type*} [Preorder ι]
    {a b c : ι} (hab : a < b) (hbc : b < c) : StrictMono ![a, b, c] :=
  (strictMono_vecEmpty.vecCons hbc).vecCons hab

/-- An above-diagonal zero can only be in the first row and last column.
The extremality conclusion does not require choosing named endpoints. -/
theorem zero_above_forces_extremes {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : NonpositiveThreeMinors Y) {i j : Fin n}
    (hij : i < j) (hz : Y i j = 0) :
    (∀ r, i ≤ r) ∧ (∀ c, c ≤ j) := by
  have hdiag := diagonal_pos_of_nonsingular hY h₂ hdet
  constructor
  · intro r
    by_contra h
    have hri : r < i := lt_of_not_ge h
    obtain ⟨a, b, hab, hpos⟩ := exists_positive_two_minor_on_rows hY h₂ hdet hri
    have hbj : b < j := by
      by_contra h
      have hjb : j ≤ b := le_of_not_gt h
      have hrb := northeast_zero hY h₂ hdiag hij hz (le_of_lt hri) hjb
      have hib := northeast_zero hY h₂ hdiag hij hz le_rfl hjb
      rw [hrb, hib] at hpos
      linarith
    have hrj := northeast_zero hY h₂ hdiag hij hz (le_of_lt hri) le_rfl
    have hneg := h₃ ![r, i, j] ![a, b, j]
      (strictMono_three hri hij) (strictMono_three hab hbj)
    have heq : Matrix.det (Y.submatrix ![r, i, j] ![a, b, j]) =
        Y j j * (Y r a * Y i b - Y r b * Y i a) := by
      rw [Matrix.det_fin_three]
      simp [hz, hrj]
      ring
    rw [heq] at hneg
    exact (not_le_of_gt (mul_pos (hdiag j) hpos)) hneg
  · intro c
    by_contra h
    have hjc : j < c := lt_of_not_ge h
    obtain ⟨r, s, hrs, hpos⟩ := exists_positive_two_minor_on_cols hY h₂ hdet hjc
    have hir : i < r := by
      by_contra h
      have hri : r ≤ i := le_of_not_gt h
      have hrj := northeast_zero hY h₂ hdiag hij hz hri le_rfl
      have hrc := northeast_zero hY h₂ hdiag hij hz hri (le_of_lt hjc)
      rw [hrj, hrc] at hpos
      linarith
    have hic := northeast_zero hY h₂ hdiag hij hz le_rfl (le_of_lt hjc)
    have hneg := h₃ ![i, r, s] ![i, j, c]
      (strictMono_three hir hrs) (strictMono_three hij hjc)
    have heq : Matrix.det (Y.submatrix ![i, r, s] ![i, j, c]) =
        Y i i * (Y r j * Y s c - Y r c * Y s j) := by
      rw [Matrix.det_fin_three]
      simp [hz, hic]
      ring
    rw [heq] at hneg
    exact (not_le_of_gt (mul_pos (hdiag i) hpos)) hneg

/-- Section 3.2: every zero is in one of the two off-diagonal extreme
corners. The quantified formulation covers all finite dimensions uniformly. -/
theorem zero_only_extreme_corners {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : NonpositiveThreeMinors Y) {i j : Fin n} (hz : Y i j = 0) :
    ((∀ r, i ≤ r) ∧ (∀ c, c ≤ j)) ∨
      ((∀ r, r ≤ i) ∧ (∀ c, j ≤ c)) := by
  rcases lt_trichotomy i j with hij | hij | hji
  · exact Or.inl (zero_above_forces_extremes hY h₂ hdet h₃ hij hz)
  · subst j
    have hpos := diagonal_pos_of_nonsingular hY h₂ hdet i
    linarith
  · have h := zero_above_forces_extremes hY.transpose h₂.transpose
      (by simpa only [Matrix.det_transpose] using hdet) h₃.transpose hji hz
    exact Or.inr ⟨h.2, h.1⟩

/-- Named-index form of the two-corner restriction in nonempty dimension. -/
theorem zero_only_corners {n : ℕ} {Y : Square (n + 1)}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : NonpositiveThreeMinors Y) {i j : Fin (n + 1)} (hz : Y i j = 0) :
    (i = 0 ∧ j = Fin.last n) ∨ (i = Fin.last n ∧ j = 0) := by
  rcases zero_only_extreme_corners hY h₂ hdet h₃ hz with h | h
  · exact Or.inl ⟨le_antisymm (h.1 0) (Fin.zero_le i),
      le_antisymm (Fin.le_last j) (h.2 (Fin.last n))⟩
  · exact Or.inr ⟨le_antisymm (Fin.le_last i) (h.1 (Fin.last n)),
      le_antisymm (h.2 0) (Fin.zero_le j)⟩

/-- There are at most two zero entries in the whole matrix. -/
theorem card_zero_entries_le_two {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : NonpositiveThreeMinors Y) :
    (Finset.univ.filter (fun ij : Fin n × Fin n => Y ij.1 ij.2 = 0)).card ≤ 2 := by
  classical
  cases n with
  | zero => simp
  | succ n =>
    have hsub :
        Finset.univ.filter (fun ij : Fin (n + 1) × Fin (n + 1) => Y ij.1 ij.2 = 0) ⊆
        {(0, Fin.last n), (Fin.last n, 0)} := by
      intro ij hij
      have hz := (Finset.mem_filter.mp hij).2
      rcases zero_only_corners hY h₂ hdet h₃ hz with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Prod.ext h.1 h.2)
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Prod.ext h.1 h.2)
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- Every entry in a nonextreme column is strictly positive. -/
theorem column_pos_of_between {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : NonpositiveThreeMinors Y) {a q c : Fin n}
    (haq : a < q) (hqc : q < c) : ∀ i, 0 < Y i q := by
  intro i
  by_contra h
  have hz : Y i q = 0 := le_antisymm (le_of_not_gt h) (hY i q)
  rcases zero_only_extreme_corners hY h₂ hdet h₃ hz with h | h
  · exact (not_le_of_gt hqc) (h.2 c)
  · exact (not_le_of_gt haq) (h.2 a)

end IV01
