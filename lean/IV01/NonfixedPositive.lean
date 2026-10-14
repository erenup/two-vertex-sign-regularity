import IV01.SchurSetup
import IV01.SchurVanishing
import IV01.Induction
import IV01.FixedIndices

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem lower_pivot_pos {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hε : IsSignature n ε) (hlow : LowerMinorSigns ε L U (p+2)) (hM : InBox L U M)
    (P Q : Fin p → Fin n) (hP : StrictMono P) (hQ : StrictMono Q)
    (hH : (M.submatrix P Q).det ≠ 0) :
    0 < pivotSignature ε p * (M.submatrix P Q).det := by
  by_cases hp : p = 0
  · subst p
    simp [pivotSignature]
  · have hpn : p ≤ n := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective P hP.injective
    have hn := mul_ne_zero (signature_ne_zero hε (by omega) hpn) hH
    have hz := hlow p (by omega) (by omega) M hM P Q hP hQ
    simpa only [pivotSignature, if_neg hp, minor] using lt_of_le_of_ne hz (Ne.symm hn)

theorem positive_bad_frame {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hpn : p+3 ≤ n) (hε : IsSignature n ε)
    (hlow : LowerMinorSigns ε L U (p+2)) (hM : InBox L U M)
    (hδ : schurThirdSign ε p = 1)
    (rows cols : Fin (p+3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : ε (p+3) * minor M rows cols < 0)
    (rp : Fin p → Fin (p+3)) (cp : Fin p → Fin (p+1))
    (hrp : StrictMono rp) (hcp : StrictMono cp)
    (f : SchurFrame rows cols rp cp)
    (hH : (M.submatrix (rows ∘ rp) (cols ∘ middleIndices ∘ cp)).det ≠ 0) :
    let T := normalizedSchur M (rows ∘ rp) (cols ∘ middleIndices ∘ cp) f.R f.C
      (pivotSignature ε p) (ε (p+1)) (ε (p+2))
    NonnegativeEntries T ∧ TP2 T ∧
      minor T (orientedRows f.r (pivotSignature ε p) (ε (p+2))) f.c < 0 := by
  have he := pivotSignature_sign hε (by omega : p ≤ n)
  have he₁ := hε (p+1) (by omega) (by omega)
  have he₂ := hε (p+2) (by omega) (by omega)
  have hP := hr.comp hrp
  have hQ := hc.comp (strictMono_middleIndices.comp hcp)
  have heH := lower_pivot_pos hε hlow hM _ _ hP hQ hH
  have hh := normalizedSchur_lower_closure M _ _ f.R f.C hP hQ f.hR f.hC
    f.disR f.disC _ _ _ he he₁ he₂ hH heH
    (hlow (p+1) (by omega) (by omega) M hM)
    (hlow (p+2) (by omega) (by omega) M hM)
  refine ⟨hh.1, hh.2, ?_⟩
  have hb := normalizedSchur_wrong_three M _ _ f.R f.C hP hQ f.hR f.hC
    (pivotSignature ε p) (ε (p+1)) (ε (p+2)) (ε (p+3)) he he₁ he₂
    f.r f.c f.hr f.hc rows cols f.σ f.τ hr hc f.sortR f.sortC hH heH hbad
  change schurThirdSign ε p * _ < 0 at hb
  simpa only [hδ, one_mul] using hb

theorem positive_bad_frame_middle_ne_zero {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hpn : p+3 ≤ n) (hε : IsSignature n ε)
    (hlow : LowerMinorSigns ε L U (p+2)) (hM : InBox L U M)
    (hδ : schurThirdSign ε p = 1)
    (rows cols : Fin (p+3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : ε (p+3) * minor M rows cols < 0)
    (rp : Fin p → Fin (p+3)) (cp : Fin p → Fin (p+1))
    (hrp : StrictMono rp) (hcp : StrictMono cp)
    (f : SchurFrame rows cols rp cp)
    (hH : (M.submatrix (rows ∘ rp) (cols ∘ middleIndices ∘ cp)).det ≠ 0) :
    ∀ i, schurAt M (rows ∘ rp) (cols ∘ middleIndices ∘ cp) f.R f.C (f.r i) (f.c 1) ≠ 0 := by
  obtain ⟨hn, ht, hb⟩ := positive_bad_frame hpn hε hlow hM hδ rows cols hr hc hbad rp cp hrp hcp f hH
  have hpos := middle_column_pos_of_three_minor_neg hn ht
    (orientedRows_strictMono f.r _ _ f.hr) f.hc hb
  intro i
  apply schurAt_entry_ne_zero_of_normalized M _ _ f.R f.C
    (pivotSignature ε p) (ε (p+1)) (ε (p+2)) (f.r i) (f.c 1)
  by_cases hs : pivotSignature ε p * ε (p+2) = 1
  · simpa only [orientedRows, if_pos hs] using (hpos i).ne'
  · simpa only [orientedRows, if_neg hs, Function.comp_apply, Fin.rev_rev] using (hpos i.rev).ne'

theorem positive_bad_no_essential_row {n p : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hpn : p+3 ≤ n) (hε : IsSignature n ε)
    (hlow : LowerMinorSigns ε L U (p+2)) (hM : InBox L U M)
    (hδ : schurThirdSign ε p = 1)
    (rows cols : Fin (p+3) → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (hbad : ε (p+3) * minor M rows cols < 0)
    (hrank : (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = p+1)
    (i : Fin (p+3))
    (hdelete : (M.submatrix
      (rows ∘ (Subtype.val : {a : Fin (p+3) // a ≠ i} → Fin (p+3)))
      (Subtype.val : InteriorColumns cols → Fin n)).rank = p) : False := by
  classical
  have hdet : minor M rows cols ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hbad
    exact (lt_irrefl 0) hbad
  let core := cols ∘ middleIndices
  let A := M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)
  let del : {a : Fin (p+3) // a ≠ i} → Fin (p+3) := Subtype.val
  have hbRank : (A.submatrix id (coreToInterior cols hc)).rank = A.rank := by
    change (M.submatrix rows core).rank = _
    rw [core_rank_of_target_det_ne_zero M rows cols hdet]
    exact hrank.symm
  have hcore := rank_row_restrict_of_column_rank_eq A (coreToInterior cols hc) del hbRank
  change (M.submatrix (rows ∘ del) core).rank =
    (M.submatrix (rows ∘ del) (Subtype.val : InteriorColumns cols → Fin n)).rank at hcore
  rw [hdelete] at hcore
  obtain ⟨r₀, cp, hr₀, hcp, hH⟩ := exists_nonzero_increasing_minor_of_le_rank
    (M.submatrix (rows ∘ del) core) p hcore.ge
  let rp : Fin p → Fin (p+3) := del ∘ r₀
  have hrp : StrictMono rp := hr₀
  change (M.submatrix (rows ∘ rp) (cols ∘ middleIndices ∘ cp)).det ≠ 0 at hH
  obtain ⟨f⟩ := exists_schurFrame (by omega : p ≤ n) rows cols hr hc rp cp hrp hcp
  have hne := positive_bad_frame_middle_ne_zero hpn hε hlow hM hδ rows cols hr hc
    hbad rp cp hrp hcp f hH
  obtain ⟨a, ha⟩ : ∃ a : Fin 3, f.rr a ≠ i := by
    by_cases h : f.rr 0 = i
    · refine ⟨1, ?_⟩
      intro hh
      have hh' : f.rr 0 = f.rr 1 := h.trans hh.symm
      exact (by decide : (0 : Fin 3) ≠ 1) (f.hrr.injective hh')
    · exact ⟨0, h⟩
  apply hne a
  apply schurAt_entry_zero_of_rectangle_rank M _ _ f.R f.C
    (rows ∘ del) (Subtype.val : InteriorColumns cols → Fin n) hH hdelete.le
  · intro t
    exact ⟨r₀ t, rfl⟩
  · intro t
    exact ⟨coreToInterior cols hc (cp t), rfl⟩
  · refine ⟨⟨f.rr a, ha⟩, ?_⟩
    exact (congrFun f.rows_eq a).symm
  · refine ⟨⟨f.C (f.c 1), ?_, ?_⟩, rfl⟩
    · rw [← f.col_first]
      exact f.hC (f.hc (by decide))
    · rw [← f.col_last]
      exact f.hC (f.hc (by decide))

end IV01
