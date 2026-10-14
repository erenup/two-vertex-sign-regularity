import IV01.NonfixedColumn

namespace IV01

/-- The positive-sign exclusion required by the all-order induction. -/
theorem positiveNonfixedRectangleExcluded : SignedNonfixedRectangleExcluded 1 := by
  classical
  intro n p ε L U hpn hε hLU hminus hplus hlower M hM rows cols hr hc
    hbad hcard hrank hbound hnonfixed hδ
  have hfree : ∃ i, ∃ c : InteriorColumns cols, L (rows i) c.val < U (rows i) c.val := by
    by_contra h
    apply hnonfixed
    intro i c
    apply le_antisymm (hLU _ _)
    exact le_of_not_gt (fun hlt => h ⟨i, c, hlt⟩)
  obtain ⟨i, c, hfree⟩ := hfree
  have hη : ε (p+1) ≠ 0 := signature_ne_zero hε (by omega) (by omega)
  rcases essential_residual_rank_on_box rows
      (Subtype.val : InteriorColumns cols → Fin n) hr (fun _ _ h => h)
      hM hrank hbound (ε (p+1)) hη
      (fun X hX a b ha hb => hlower (p+1) (by omega) (by omega) X hX a b ha hb)
      i c hfree with ⟨hrow, _⟩ | ⟨hcol, _⟩
  · exact positive_bad_no_essential_row hpn hε hlower hM.1 hδ rows cols hr hc
      hbad hrank i hrow
  · exact positive_bad_no_essential_column hpn hε hlower hM.1 hδ rows cols hr hc
      hbad hrank (inBox_nonsingular hε hminus hplus hM.1) hcard c hcol

end IV01
