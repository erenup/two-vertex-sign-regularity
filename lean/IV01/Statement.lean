import IV01.Definitions
import IV01.FixedAdapter
import IV01.PositiveExclusion
import IV01.NegativeExclusion

/-!
# The two-checker-vertex theorem (IV-01)

The target covers every positive dimension, every real box, and every
signature in `{-1, 1}^n`. Sign regularity is weak: zero proper minors are
allowed. The only nonsingularity assumptions concern the two checker
vertices, and the conclusion includes nonsingularity of every box matrix.
-/

namespace IV01

theorem twoCheckerVertices
    (n : ℕ) (hn : 1 ≤ n) (ε : ℕ → ℝ) (hε : IsSignature n ε)
    (L U : Square n) (hLU : EntrywiseLE L U)
    (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hplus : NonsingularSignRegular ε (checkerPlus L U))
    (M : Square n) (hM : InBox L U M) :
    NonsingularSignRegular ε M := by
  exact nonsingularSignRegular_of_rectangle_exclusions
    fixedRectangleExcluded positiveNonfixedRectangleExcluded negativeNonfixedRectangleExcluded
    hε hLU hminus hplus hM

end IV01
