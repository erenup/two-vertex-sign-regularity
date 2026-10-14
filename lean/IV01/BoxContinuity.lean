import IV01.Box
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Instances.Real.Lemmas

set_option backward.isDefEq.respectTransparency false

namespace IV01

noncomputable def towardMidpoint {n : ℕ} (L U X : Square n) (t : ℝ) : Square n :=
  fun i j => (1 - t) * X i j + t * boxMidpoint L U i j

theorem towardMidpoint_interior {n : ℕ} {L U X : Square n}
    (hLU : EntrywiseLE L U) (hX : InBox L U X) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) : InRelativeInterior L U (towardMidpoint L U X t) := by
  have hmid := boxMidpoint_interior hLU
  constructor
  · constructor <;> intro i j <;> dsimp [towardMidpoint]
    · have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hX.1 i j))
      have h₂ := mul_nonneg ht0.le (sub_nonneg.mpr (hmid.1.1 i j))
      nlinarith
    · have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hX.2 i j))
      have h₂ := mul_nonneg ht0.le (sub_nonneg.mpr (hmid.1.2 i j))
      nlinarith
  · intro i j hij
    dsimp [towardMidpoint]
    constructor
    · have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hX.1 i j))
      have h₂ := mul_pos ht0 (sub_pos.mpr (hmid.2 i j hij).1)
      nlinarith
    · have h₁ := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (hX.2 i j))
      have h₂ := mul_pos ht0 (sub_pos.mpr (hmid.2 i j hij).2)
      nlinarith

/-- Weak minor signs on the relative interior extend to every boundary point. -/
theorem signed_minor_nonneg_on_box {n k : ℕ} {L U X : Square n}
    (hLU : EntrywiseLE L U) (rows cols : Fin k → Fin n) (s : ℝ)
    (hint : ∀ M, InRelativeInterior L U M → 0 ≤ s * minor M rows cols)
    (hX : InBox L U X) : 0 ≤ s * minor X rows cols := by
  have hclosure : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, by norm_num⟩
  have hcont : Continuous (fun t : ℝ => s * minor (towardMidpoint L U X t) rows cols) := by
    unfold minor towardMidpoint
    fun_prop
  have h := ContinuousWithinAt.closure_le hclosure
    (continuous_const.continuousWithinAt : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) _ _)
    hcont.continuousWithinAt
    (fun t ht => hint _ (towardMidpoint_interior hLU hX ht.1 ht.2.le))
  have hzero : towardMidpoint L U X 0 = X := by
    ext i j
    simp [towardMidpoint]
  rwa [hzero] at h

theorem exists_interior_bad_minor {n k : ℕ} {L U X : Square n}
    (hLU : EntrywiseLE L U) (rows cols : Fin k → Fin n) (s : ℝ)
    (hX : InBox L U X) (hbad : s * minor X rows cols < 0) :
    ∃ M, InRelativeInterior L U M ∧ s * minor M rows cols < 0 := by
  by_contra! h
  have hnonneg := signed_minor_nonneg_on_box hLU rows cols s h hX
  linarith

end IV01
