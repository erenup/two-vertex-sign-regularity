import IV01.NonfixedPositive

set_option backward.isDefEq.respectTransparency false

namespace IV01

open Matrix Module

/-- The positive-third-sign case cannot have an essential interior column.
All pivot indices are chosen inside the actual bad target minor. -/
theorem positive_bad_no_essential_column {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hpn : p+3 ≤ n) (hε : IsSignature n ε)
    (hlow : LowerMinorSigns ε L U (p+2)) (hM : InBox L U M)
    (hδ : schurThirdSign ε p = 1)
    (rows cols : Fin (p+3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : ε (p+3) * minor M rows cols < 0)
    (hrank : (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = p+1)
    (hMdet : M.det ≠ 0) (hcard : p+2 ≤ Fintype.card (InteriorColumns cols))
    (j : InteriorColumns cols)
    (hdelete : (M.submatrix rows
      ((Subtype.val : InteriorColumns cols → Fin n) ∘
        (Subtype.val : {b : InteriorColumns cols // b ≠ j} → InteriorColumns cols))).rank = p) :
    False := by
  classical
  have hdet : minor M rows cols ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hbad
    exact (lt_irrefl 0) hbad
  let A := M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)
  let core := cols ∘ middleIndices
  let del : {b : InteriorColumns cols // b ≠ j} → Fin n :=
    (Subtype.val : InteriorColumns cols → Fin n) ∘ Subtype.val
  have hbRank : (A.submatrix id (coreToInterior cols hc)).rank = A.rank := by
    change (M.submatrix rows core).rank = _
    rw [core_rank_of_target_det_ne_zero M rows cols hdet]
    exact hrank.symm
  have hessential : (A.submatrix id
      (Subtype.val : {b : InteriorColumns cols // b ≠ j} → InteriorColumns cols)).rank < A.rank := by
    change (M.submatrix rows del).rank < _
    rw [hdelete]
    change p < (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank
    rw [hrank]
    omega
  obtain ⟨j₀, hj₀⟩ := essential_column_mem_range A (coreToInterior cols hc) j hbRank hessential
  have hjval : core j₀ = j.val := congrArg Subtype.val hj₀
  let cp : Fin p → Fin (p+1) := j₀.succAbove
  have hcp : StrictMono cp := Fin.strictMono_succAbove j₀
  have hQdel : ∀ t, (cols ∘ middleIndices ∘ cp) t ∈ Set.range del := by
    intro t
    refine ⟨⟨coreToInterior cols hc (cp t), ?_⟩, rfl⟩
    intro h
    have hh : cp t = j₀ := (hc.comp strictMono_middleIndices).injective
      ((congrArg Subtype.val h).trans hjval.symm)
    exact Fin.succAbove_ne j₀ t hh
  let K := M.submatrix rows (cols ∘ middleIndices ∘ cp)
  have hKrank : K.rank = p := by
    have hli := (Matrix.linearIndependent_cols_of_det_ne_zero hdet).comp
      (middleIndices ∘ cp) (strictMono_middleIndices.injective.comp hcp.injective)
    rw [Matrix.rank_eq_finrank_span_cols]
    have hh := linearIndependent_iff_card_eq_finrank_span.mp hli
    change finrank ℝ (Submodule.span ℝ
      (Set.range ((M.submatrix rows cols).col ∘ (middleIndices ∘ cp)))) = p
    simpa only [Set.finrank, Fintype.card_fin] using hh.symm
  obtain ⟨rp, hrp, hli⟩ := exists_strictMono_independent_subfamily_of_le_finrank_span
    K.row p (by rw [← Matrix.rank_eq_finrank_span_row, hKrank])
  have hH : (M.submatrix (rows ∘ rp) (cols ∘ middleIndices ∘ cp)).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp
      ((M.submatrix (rows ∘ rp) (cols ∘ middleIndices ∘ cp)).isUnit_iff_isUnit_det.mp
        (Matrix.linearIndependent_rows_iff_isUnit.mp hli))
  obtain ⟨f⟩ := exists_schurFrame (by omega : p ≤ n) rows cols hr hc rp cp hrp hcp
  obtain ⟨hn, ht, hb⟩ := positive_bad_frame hpn hε hlow hM hδ rows cols hr hc hbad
    rp cp hrp hcp f hH
  let e := pivotSignature ε p
  let T := normalizedSchur M (rows ∘ rp) (cols ∘ middleIndices ∘ cp) f.R f.C
    e (ε (p+1)) (ε (p+2))
  have he : e ≠ 0 := by
    rcases pivotSignature_sign hε (show p ≤ n by omega) with h | h <;> simp [e, h]
  have hTdet : T.det ≠ 0 := normalizedSchur_nonsingular_of_le (by omega) M
    (rows ∘ rp) (cols ∘ middleIndices ∘ cp) f.R f.C (hr.comp hrp).injective
    (hc.comp (strictMono_middleIndices.comp hcp)).injective f.hR.injective f.hC.injective
    f.disR f.disC e (ε (p+1)) (ε (p+2))
    (mul_ne_zero he (signature_ne_zero hε (by omega) (by omega))) hMdet hH
  obtain ⟨b, hbcore⟩ := exists_extra_interior_column cols hc hcard
  have hbj : b ≠ j := by
    intro hh
    apply hbcore
    exact ⟨j₀, hjval.trans (congrArg Subtype.val hh).symm⟩
  have hbQ : b.val ∉ Set.range (cols ∘ middleIndices ∘ cp) := by
    rintro ⟨t, ht⟩
    exact hbcore ⟨cp t, ht⟩
  obtain ⟨b₀, hb₀⟩ := (f.compC b.val).mpr hbQ
  have hleft : f.c 0 < b₀ := by
    apply f.hC.lt_iff_lt.mp
    rw [f.col_first, hb₀]
    exact b.property.1
  have hright : b₀ < f.c 2 := by
    apply f.hC.lt_iff_lt.mp
    rw [f.col_last, hb₀]
    exact b.property.2
  have hmiddle : f.C (f.c 1) ∈ Set.range core := by
    apply (mem_range_middle_iff cols hc _).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨f.cc 1, (congrFun f.cols_eq 1).symm⟩
    · rw [← f.col_first]
      exact f.hC (f.hc (by decide))
    · rw [← f.col_last]
      exact f.hC (f.hc (by decide))
  have hbmid : b₀ ≠ f.c 1 := by
    intro hh
    apply hbcore
    rw [← hb₀, hh]
    exact hmiddle
  have hzero : ∀ a, schurAt M (rows ∘ rp) (cols ∘ middleIndices ∘ cp)
      f.R f.C (f.r a) b₀ = 0 := by
    intro a
    apply schurAt_entry_zero_of_rectangle_rank M _ _ f.R f.C rows del hH hdelete.le
    · intro t
      exact ⟨rp t, rfl⟩
    · exact hQdel
    · exact ⟨f.rr a, (congrFun f.rows_eq a).symm⟩
    · exact ⟨⟨b, hbj⟩, hb₀.symm⟩
  exact no_negative_three_of_zero_interior_column hn ht hTdet
    (orientedRows f.r e (ε (p+2))) f.c (orientedRows_strictMono f.r _ _ f.hr) f.hc
    hb b₀ hleft hright hbmid
    (normalizedSchur_selected_column_zero M _ _ f.R f.C e (ε (p+1)) (ε (p+2)) f.r b₀ hzero)

end IV01
