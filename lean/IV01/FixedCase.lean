import IV01.FixedIndices
import IV01.SchurVanishing

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem fixed_rectangle_submatrix_eq {n : ℕ} {α β ρ κ : Type*}
    {L U X Y : Square n} (hX : InBox L U X) (hY : InBox L U Y)
    (rows : α → Fin n) (cols : β → Fin n)
    (hfixed : ∀ i j, L (rows i) (cols j) = U (rows i) (cols j))
    (r : ρ → Fin n) (c : κ → Fin n)
    (hr : ∀ i, r i ∈ Set.range rows) (hc : ∀ j, c j ∈ Set.range cols) :
    X.submatrix r c = Y.submatrix r c := by
  ext i j
  obtain ⟨a, ha⟩ := hr i
  obtain ⟨b, hb⟩ := hc j
  have hf : L (r i) (c j) = U (r i) (c j) := by
    rw [← ha, ← hb]
    exact hfixed a b
  have hx₁ := hX.1 (r i) (c j)
  have hx₂ := hX.2 (r i) (c j)
  have hy₁ := hY.1 (r i) (c j)
  have hy₂ := hY.2 (r i) (c j)
  change X (r i) (c j) = Y (r i) (c j)
  linarith

theorem SchurFrame.middle_mem_core {n p : ℕ}
    {rows cols : Fin (p+3) → Fin n} {rp : Fin p → Fin (p+3)}
    {cp : Fin p → Fin (p+1)} (F : SchurFrame rows cols rp cp)
    (hcols : StrictMono cols) : F.C (F.c 1) ∈ Set.range (cols ∘ middleIndices) := by
  apply (mem_range_middle_iff cols hcols _).mpr
  refine ⟨⟨F.cc 1, (congrFun F.cols_eq 1).symm⟩, ?_, ?_⟩
  · rw [← F.col_first]
    exact F.hC (F.hc (by decide))
  · rw [← F.col_last]
    exact F.hC (F.hc (by decide))

theorem SchurFrame.extra_column {n p : ℕ}
    {rows cols : Fin (p+3) → Fin n} {rp : Fin p → Fin (p+3)}
    {cp : Fin p → Fin (p+1)} (F : SchurFrame rows cols rp cp)
    (hcols : StrictMono cols) (hcard : p+2 ≤ Fintype.card (InteriorColumns cols)) :
    ∃ b : Fin (n-p), F.c 0 < b ∧ b < F.c 2 ∧ b ≠ F.c 1 ∧
      F.C b ∉ Set.range (cols ∘ middleIndices) := by
  obtain ⟨b, hb⟩ := exists_extra_interior_column cols hcols hcard
  have hbC : b.val ∈ Set.range F.C := by
    apply (F.compC _).mpr
    rintro ⟨i, hi⟩
    exact hb ⟨cp i, hi⟩
  obtain ⟨b', hb'⟩ := hbC
  refine ⟨b', ?_, ?_, ?_, ?_⟩
  · apply F.hC.lt_iff_lt.mp
    rw [F.col_first, hb']
    exact b.property.1
  · apply F.hC.lt_iff_lt.mp
    rw [F.col_last, hb']
    exact b.property.2
  · intro heq
    apply hb
    rw [← hb', heq]
    exact F.middle_mem_core hcols
  · rwa [hb']

theorem pair_indices_injective {α : Type*} {a b : α} (h : a ≠ b) :
    Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact (h hij).elim
  · exact (h hij.symm).elim
  · rfl

theorem SchurFrame.sort_pair_drop_last {n p : ℕ}
    {rows cols : Fin (p+3) → Fin n} {rp : Fin p → Fin (p+3)}
    {cp : Fin p → Fin (p+1)} (F : SchurFrame rows cols rp cp)
    (hcols : StrictMono cols) (hcp : StrictMono cp) :
    ∃ τ : Equiv.Perm (Fin (p+2)),
      appendIndices (cols ∘ middleIndices ∘ cp) (F.C ∘ ![F.c 1, F.c 0]) =
        (cols ∘ Fin.castSucc) ∘ τ := by
  apply exists_perm_of_range_subset
  · apply appendIndices_injective
    · exact (hcols.comp (strictMono_middleIndices.comp hcp)).injective
    · exact F.hC.injective.comp (pair_indices_injective (ne_of_gt (F.hc (by decide))))
    · exact fun i j => F.disC i (![F.c 1, F.c 0] j)
  · exact (hcols.comp Fin.strictMono_castSucc).injective
  · intro j
    unfold appendIndices
    cases finSumFinEquiv.symm j with
    | inl i =>
      apply mem_range_drop_last cols ⟨middleIndices (cp i), rfl⟩
      exact ne_of_lt (hcols (middleIndices_lt_last (cp i)))
    | inr i =>
      fin_cases i
      · apply mem_range_drop_last cols
        · exact ⟨F.cc 1, (congrFun F.cols_eq 1).symm⟩
        · change F.C (F.c 1) ≠ cols (Fin.last (p+2))
          rw [← F.col_last]
          exact ne_of_lt (F.hC (F.hc (by decide)))
      · apply mem_range_drop_last cols
        · exact ⟨F.cc 0, (congrFun F.cols_eq 0).symm⟩
        · change F.C (F.c 0) ≠ cols (Fin.last (p+2))
          rw [← F.col_last]
          exact ne_of_lt (F.hC (F.hc (by decide)))

theorem SchurFrame.sort_pair_drop_first {n p : ℕ}
    {rows cols : Fin (p+3) → Fin n} {rp : Fin p → Fin (p+3)}
    {cp : Fin p → Fin (p+1)} (F : SchurFrame rows cols rp cp)
    (hcols : StrictMono cols) (hcp : StrictMono cp) :
    ∃ τ : Equiv.Perm (Fin (p+2)),
      appendIndices (cols ∘ middleIndices ∘ cp) (F.C ∘ ![F.c 1, F.c 2]) =
        (cols ∘ Fin.succ) ∘ τ := by
  apply exists_perm_of_range_subset
  · apply appendIndices_injective
    · exact (hcols.comp (strictMono_middleIndices.comp hcp)).injective
    · exact F.hC.injective.comp (pair_indices_injective (ne_of_lt (F.hc (by decide))))
    · exact fun i j => F.disC i (![F.c 1, F.c 2] j)
  · exact (hcols.comp Fin.strictMono_succ).injective
  · intro j
    unfold appendIndices
    cases finSumFinEquiv.symm j with
    | inl i =>
      apply mem_range_drop_first cols ⟨middleIndices (cp i), rfl⟩
      exact ne_of_gt (hcols (middleIndices_pos (cp i)))
    | inr i =>
      fin_cases i
      · apply mem_range_drop_first cols
        · exact ⟨F.cc 1, (congrFun F.cols_eq 1).symm⟩
        · change F.C (F.c 1) ≠ cols 0
          rw [← F.col_first]
          exact ne_of_gt (F.hC (F.hc (by decide)))
      · apply mem_range_drop_first cols
        · exact ⟨F.cc 2, (congrFun F.cols_eq 2).symm⟩
        · change F.C (F.c 2) ≠ cols 0
          rw [← F.col_first]
          exact ne_of_gt (F.hC (F.hc (by decide)))

/-- A fixed minimal-bad interior rectangle is impossible. The pivot is
selected from its full-rank core; no Schur data are assumed. -/
theorem fixed_rectangle_case {n p : ℕ} {L U M : Square n}
    (hLU : EntrywiseLE L U) (hn : p+3 ≤ n)
    (s₁ s₂ s₃ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) (hs₃ : s₃ = 1 ∨ s₃ = -1)
    (h₁ : ∀ X, InBox L U X → HasSignedMinors X (p+1) s₁)
    (h₂ : ∀ X, InBox L U X → HasSignedMinors X (p+2) s₂)
    (hminus : (checkerMinus L U).det ≠ 0) (hplus : (checkerPlus L U).det ≠ 0)
    (hminus₃ : HasSignedMinors (checkerMinus L U) (p+3) s₃)
    (hplus₃ : HasSignedMinors (checkerPlus L U) (p+3) s₃)
    (hM : InBox L U M) (hMdet : M.det ≠ 0)
    (rows cols : Fin (p+3) → Fin n) (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hbad : s₃ * minor M rows cols < 0)
    (hcard : p+2 ≤ Fintype.card (InteriorColumns cols))
    (hrank : (M.submatrix rows (fun c : InteriorColumns cols => c.val)).rank ≤ p+1)
    (hfixed : ∀ i (c : InteriorColumns cols), L (rows i) c.val = U (rows i) c.val) :
    False := by
  classical
  have htarget : minor M rows cols ≠ 0 := by intro h; rw [h, mul_zero] at hbad; linarith
  have hcore := core_rank_of_target_det_ne_zero M rows cols htarget
  obtain ⟨rp, cp, hrp, hcp, hH⟩ := exists_nonzero_increasing_minor_of_le_rank
    (M.submatrix rows (cols ∘ middleIndices)) p (by rw [hcore]; omega)
  let P := rows ∘ rp
  let Q := cols ∘ middleIndices ∘ cp
  have hP : StrictMono P := hrows.comp hrp
  have hQ : StrictMono Q := hcols.comp (strictMono_middleIndices.comp hcp)
  change (M.submatrix P Q).det ≠ 0 at hH
  obtain ⟨F⟩ := exists_schurFrame (by omega : p ≤ n) rows cols hrows hcols rp cp hrp hcp
  obtain ⟨b, hab, hbc, hbq, _⟩ := F.extra_column hcols hcard
  have hPmem : ∀ i, P i ∈ Set.range rows := fun i => ⟨rp i, rfl⟩
  have hRmem : ∀ i, (F.R ∘ F.r) i ∈ Set.range rows :=
    fun i => ⟨F.rr i, (congrFun F.rows_eq i).symm⟩
  have hQmem : ∀ i, Q i ∈ Set.range (fun c : InteriorColumns cols => c.val) :=
    fun i => ⟨coreToInterior cols hcols (cp i), rfl⟩
  have hBmem : ∀ j, (F.C ∘ ![F.c 1, b]) j ∈
      Set.range (fun c : InteriorColumns cols => c.val) := by
    intro j
    fin_cases j
    · refine ⟨⟨F.C (F.c 1), ?_, ?_⟩, rfl⟩
      · rw [← F.col_first]; exact F.hC (F.hc (by decide))
      · rw [← F.col_last]; exact F.hC (F.hc (by decide))
    · refine ⟨⟨F.C b, ?_, ?_⟩, rfl⟩
      · rw [← F.col_first]; exact F.hC hab
      · rw [← F.col_last]; exact F.hC hbc
  have hHfixed : ∀ X, InBox L U X → X.submatrix P Q = M.submatrix P Q := by
    intro X hX
    exact fixed_rectangle_submatrix_eq hX hM rows _ hfixed P Q hPmem hQmem
  obtain ⟨e, he, heH⟩ : ∃ e : ℝ, (e=1 ∨ e= -1) ∧ 0 < e * (M.submatrix P Q).det := by
    rcases lt_or_gt_of_ne hH with hneg | hpos
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hpos⟩
  have ha : e * s₁ ≠ 0 := by
    rcases sign_product he hs₁ with h | h <;> rw [h] <;> norm_num
  let T := fun X : Square n => normalizedSchur X P Q F.R F.C e s₁ s₂
  let rr := orientedRows F.r e s₂
  have hrr : StrictMono rr := orientedRows_strictMono F.r e s₂ F.hr
  have hnorm : ∀ X, InBox L U X → X.det ≠ 0 →
      NonnegativeEntries (T X) ∧ TP2 (T X) ∧ (T X).det ≠ 0 := by
    intro X hX hXd
    have hHX : (X.submatrix P Q).det ≠ 0 := by rw [hHfixed X hX]; exact hH
    have heHX : 0 < e * (X.submatrix P Q).det := by rw [hHfixed X hX]; exact heH
    obtain ⟨hpos, htp⟩ := normalizedSchur_lower_closure X P Q F.R F.C
      hP hQ F.hR F.hC F.disR F.disC e s₁ s₂ he hs₁ hs₂ hHX heHX (h₁ X hX) (h₂ X hX)
    exact ⟨hpos, htp, normalizedSchur_nonsingular_of_le (by omega) X P Q F.R F.C
      hP.injective hQ.injective F.hR.injective F.hC.injective F.disR F.disC
      e s₁ s₂ ha hXd hHX⟩
  have hAb := checkerMinus_mem_box hLU
  have hBb := checkerPlus_mem_box hLU
  have hA := hnorm _ hAb hminus
  have hB := hnorm _ hBb hplus
  have hT := hnorm M hM hMdet
  have hthree : ∀ X, InBox L U X → HasSignedMinors X (p+3) s₃ →
      SignedThreeMinors (e*s₁*s₂*s₃) (T X) := by
    intro X hX hX₃
    exact normalizedSchur_third_closure X P Q F.R F.C hP hQ F.hR F.hC F.disR F.disC
      e s₁ s₂ s₃ he hs₁ hs₂ (by rw [hHfixed X hX]; exact hH)
      (by rw [hHfixed X hX]; exact heH) hX₃
  have hpairSource : (M.submatrix (appendIndices P (F.R ∘ F.r))
      (appendIndices Q (F.C ∘ ![F.c 1, b]))).rank ≤ p+1 := by
    apply (rank_submatrix_le_of_ranges M rows (fun c : InteriorColumns cols => c.val)
      _ _ ?_ ?_).trans hrank
    · intro i
      unfold appendIndices
      cases finSumFinEquiv.symm i with
      | inl i => exact hPmem i
      | inr i => exact hRmem i
    · intro j
      unfold appendIndices
      cases finSumFinEquiv.symm j with
      | inl j => exact hQmem j
      | inr j => exact hBmem j
  have hpair : ((T M).submatrix rr ![F.c 1, b]).rank ≤ 1 :=
    normalized_rank_le_one_of_source_rank_le_pivot_add_one M P Q F.R F.C e s₁ s₂
      F.r ![F.c 1, b] hH ha hpairSource
  have hblock : ∀ X, InBox L U X → (T X).submatrix rr ![F.c 1, b] =
      (T M).submatrix rr ![F.c 1, b] := by
    intro X hX
    apply normalizedSchur_block_eq_of_blocks_eq P Q F.R F.C e s₁ s₂ F.r ![F.c 1, b]
    · exact hHfixed X hX
    · exact fixed_rectangle_submatrix_eq hX hM rows _ hfixed _ _ hRmem hQmem
    · exact fixed_rectangle_submatrix_eq hX hM rows _ hfixed _ _ hPmem hBmem
    · exact fixed_rectangle_submatrix_eq hX hM rows _ hfixed _ _ hRmem hBmem
  have hfix : ∀ X, InBox L U X → ∀ i j, j = F.c 1 ∨ j = b →
      T X (rr i) j = T M (rr i) j := by
    intro X hX i j hj
    rcases hj with rfl | rfl
    · exact congrArg (fun Z : Matrix (Fin 3) (Fin 2) ℝ => Z i 0) (hblock X hX)
    · exact congrArg (fun Z : Matrix (Fin 3) (Fin 2) ℝ => Z i 1) (hblock X hX)
  have hcvec : F.c = ![F.c 0, F.c 1, F.c 2] := by ext i; fin_cases i <;> rfl
  have hbadT : (e*s₁*s₂*s₃) * Matrix.det ((T M).submatrix rr ![F.c 0, F.c 1, F.c 2]) < 0 := by
    have hh := normalizedSchur_wrong_three M P Q F.R F.C hP hQ F.hR F.hC
      e s₁ s₂ s₃ he hs₁ hs₂ F.r F.c F.hr F.hc rows cols F.σ F.τ hrows hcols
      F.sortR F.sortC hH heH hbad
    change (e*s₁*s₂*s₃) * Matrix.det ((T M).submatrix rr F.c) < 0 at hh
    rwa [hcvec] at hh
  obtain ⟨d, hd, hAd, hBd⟩ := fixed_pair_common_outer_rank
    hA.1 hB.1 hT.1 hA.2.1 hB.2.1 hT.2.1 hA.2.2 hB.2.2 hT.2.2
    (hthree _ hAb hminus₃) (hthree _ hBb hplus₃)
    (sign_product (sign_product (sign_product he hs₁) hs₂) hs₃)
    rr hrr hab hbc (F.hc (by decide)) (F.hc (by decide)) hbq hpair
    (hfix _ hAb) (hfix _ hBb) hbadT
  have hfinish (cc : Fin (p+2) → Fin (p+3)) (hcc : StrictMono cc)
      (j₀ : Fin (p+2))
      (hfixed' : ∀ i j, j ≠ j₀ → L (rows i) (cols (cc j)) = U (rows i) (cols (cc j)))
      (τ : Equiv.Perm (Fin (p+2)))
      (hsort : appendIndices Q (F.C ∘ ![F.c 1, d]) = (cols ∘ cc) ∘ τ) : False := by
    have hArank := sorted_source_rank_le_pivot_add_one_of_normalized_rank_le_one
      (checkerMinus L U) P Q F.R F.C e s₁ s₂ F.r ![F.c 1, d]
      rows (cols ∘ cc) F.σ τ F.sortR hsort
      (by rw [hHfixed _ hAb]; exact hH) ha hAd
    have hBrank := sorted_source_rank_le_pivot_add_one_of_normalized_rank_le_one
      (checkerPlus L U) P Q F.R F.C e s₁ s₂ F.r ![F.c 1, d]
      rows (cols ∘ cc) F.σ τ F.sortR hsort
      (by rw [hHfixed _ hBb]; exact hH) ha hBd
    have hs₂ne : s₂ ≠ 0 := by rcases hs₂ with rfl | rfl <;> norm_num
    exact htarget (fixed_endpoint_extension_forces_target_zero hLU rows cols hrows hcols
      cc hcc j₀ hfixed' s₂ hs₂ne h₂ hArank hBrank hM)
  rcases hd with rfl | rfl
  · obtain ⟨τ, hτ⟩ := F.sort_pair_drop_last hcols hcp
    apply hfinish Fin.castSucc Fin.strictMono_castSucc 0 ?_ τ hτ
    intro i j hj
    apply hfixed i ⟨cols j.castSucc, ?_, ?_⟩
    · apply hcols
      change 0 < j.val
      have hjv : j.val ≠ 0 := fun heq => hj (Fin.ext heq)
      omega
    · exact hcols (Fin.castSucc_lt_last j)
  · obtain ⟨τ, hτ⟩ := F.sort_pair_drop_first hcols hcp
    apply hfinish Fin.succ Fin.strictMono_succ (Fin.last (p+1)) ?_ τ hτ
    intro i j hj
    apply hfixed i ⟨cols j.succ, ?_, ?_⟩
    · exact hcols (Fin.succ_pos j)
    · apply hcols
      change j.val + 1 < p+2
      have hjv : j.val ≠ p+1 := fun heq => hj (Fin.ext heq)
      have := j.isLt
      omega

end IV01
