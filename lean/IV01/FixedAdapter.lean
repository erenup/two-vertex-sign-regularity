import IV01.FixedCase
import IV01.Induction

namespace IV01

/-- The fixed rectangle exclusion required by the all-order induction. -/
theorem fixedRectangleExcluded : FixedRectangleExcluded := by
  intro n p ε L U hpn hε hLU hminus hplus hlower M hM rows cols hr hc
    hbad hcard hrank _hbound hfixed
  exact fixed_rectangle_case hLU hpn (ε (p+1)) (ε (p+2)) (ε (p+3))
    (hε _ (by omega) (by omega)) (hε _ (by omega) (by omega)) (hε _ (by omega) hpn)
    (fun X hX => hlower (p+1) (by omega) (by omega) X hX)
    (fun X hX => hlower (p+2) (by omega) (by omega) X hX)
    hminus.1 hplus.1
    (hminus.2.hasSignedMinors (by omega) hpn) (hplus.2.hasSignedMinors (by omega) hpn)
    hM.1 (inBox_nonsingular hε hminus hplus hM.1)
    rows cols hr hc hbad hcard hrank.le hfixed

end IV01
