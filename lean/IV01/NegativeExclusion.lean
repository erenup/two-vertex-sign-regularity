import IV01.NegativeThird
import IV01.Induction

namespace IV01

/-- The negative-sign exclusion required by the all-order induction. -/
theorem negativeNonfixedRectangleExcluded : SignedNonfixedRectangleExcluded (-1) := by
  classical
  intro n p ε L U hpn hε hLU hminus _hplus hlower M hM rows cols hr _hc
    _hbad hcard hrank hbound hnonfixed hδ
  have hfree : ∃ i, ∃ c : InteriorColumns cols, L (rows i) c.val < U (rows i) c.val := by
    by_contra h
    apply hnonfixed
    intro i c
    apply le_antisymm (hLU _ _)
    exact le_of_not_gt (fun hlt => h ⟨i, c, hlt⟩)
  obtain ⟨i, c, hfree⟩ := hfree
  exact negative_third_free_rectangle_contradiction rows
    (Subtype.val : InteriorColumns cols → Fin n) hr (fun _ _ h => h)
    hε hminus hpn (by simp) hcard hM hrank hbound
    (fun X hX a b ha hb => hlower (p + 1) (by omega) (by omega) X hX a b ha hb)
    hδ i c hfree

end IV01
