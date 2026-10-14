import IV01.Anchor
import IV01.Box
import IV01.SchurRank
import IV01.SchurClosure
import IV01.RankMinors

/-!
# Fixed interior rectangles

The first part is stated on the normalized Schur matrices. It proves that
the two endpoint rank-one corners extend to the same outer column.
-/

namespace IV01

theorem RankOneOn.submatrix_rank_le_one {ι κ ρ σ : Type*}
    [Fintype ι] [Fintype κ] [Fintype ρ] [Fintype σ]
    {Y : Matrix ι κ ℝ} {R : ι → Prop} {C : κ → Prop}
    (h : RankOneOn Y R C) (rows : ρ → ι) (cols : σ → κ)
    (hr : ∀ r, R (rows r)) (hc : ∀ c, C (cols c)) :
    (Y.submatrix rows cols).rank ≤ 1 := by
  obtain ⟨u, v, huv⟩ := h
  have heq : Y.submatrix rows cols = Matrix.vecMulVec (u ∘ rows) (v ∘ cols) := by
    ext r c
    exact huv _ (hr r) _ (hc c)
  rw [heq]
  exact Matrix.rank_vecMulVec_le _ _

theorem RankOneOn.mono {ι κ : Type*} {Y : Matrix ι κ ℝ}
    {R R' : ι → Prop} {C C' : κ → Prop}
    (h : RankOneOn Y R C) (hr : ∀ r, R' r → R r) (hc : ∀ c, C' c → C c) :
    RankOneOn Y R' C' := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨u, v, fun r hr' c hc' => huv r (hr r hr') c (hc c hc')⟩

/-- A common attached corner contains one common outer column and every
selected middle column between the two anchor columns. -/
theorem common_outer_column_of_common_corner {n : ℕ} {A B : Square n} {η : ℝ}
    (hη : η = 1 ∨ η = -1) {i j a k q l c : Fin n}
    (hak : a < k) (hkq : k ≤ q) (hql : q ≤ l) (hlc : l < c)
    (hcorner :
      (RankOneOn A (fun r => r ≤ j) (TopCornerColumns η k l) ∧
        RankOneOn B (fun r => r ≤ j) (TopCornerColumns η k l)) ∨
      (RankOneOn A (fun r => i ≤ r) (BottomCornerColumns η k l) ∧
        RankOneOn B (fun r => i ≤ r) (BottomCornerColumns η k l))) :
    ∃ d, (d = a ∨ d = c) ∧
      RankOneOn A (fun r => i ≤ r ∧ r ≤ j) (fun t => t = q ∨ t = d) ∧
      RankOneOn B (fun r => i ≤ r ∧ r ≤ j) (fun t => t = q ∨ t = d) := by
  have hkl : k ≤ l := hkq.trans hql
  rcases hcorner with ⟨hat, hbt⟩ | ⟨hab, hbb⟩
  · rcases hη with hη | hη
    · refine ⟨c, Or.inr rfl, ?_, ?_⟩
      all_goals
        apply RankOneOn.mono (by assumption) (fun _ h => h.2)
        intro t ht
        rcases ht with rfl | rfl
        · exact Or.inl ⟨hη, hkq⟩
        · exact Or.inl ⟨hη, hkl.trans hlc.le⟩
    · refine ⟨a, Or.inl rfl, ?_, ?_⟩
      all_goals
        apply RankOneOn.mono (by assumption) (fun _ h => h.2)
        intro t ht
        rcases ht with rfl | rfl
        · exact Or.inr ⟨hη, hql⟩
        · exact Or.inr ⟨hη, hak.le.trans hkl⟩
  · rcases hη with hη | hη
    · refine ⟨a, Or.inl rfl, ?_, ?_⟩
      all_goals
        apply RankOneOn.mono (by assumption) (fun _ h => h.1)
        intro t ht
        rcases ht with rfl | rfl
        · exact Or.inl ⟨hη, hql⟩
        · exact Or.inl ⟨hη, hak.le.trans hkl⟩
    · refine ⟨c, Or.inr rfl, ?_, ?_⟩
      all_goals
        apply RankOneOn.mono (by assumption) (fun _ h => h.1)
        intro t ht
        rcases ht with rfl | rfl
        · exact Or.inr ⟨hη, hkq⟩
        · exact Or.inr ⟨hη, hkl.trans hlc.le⟩

theorem two_cross_zero_of_rank_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Y : Matrix ι κ ℝ) (hrank : Y.rank ≤ 1) (r s : ι) (k l : κ) :
    Y r k * Y s l - Y r l * Y s k = 0 := by
  have hd : Matrix.det (Y.submatrix ![r, s] ![k, l]) = 0 := by
    by_contra hd
    have hsize := Matrix.rank_of_det_ne_zero hd
    have hle := Y.rank_submatrix_le ![r, s] ![k, l]
    simp only [hsize, Fintype.card_fin] at hle
    omega
  rw [Matrix.det_fin_two] at hd
  simpa using hd

/-- In a rank-one interior pair, a negative target three-minor forces the
second interior column to be positive on all three selected rows as well. -/
theorem interior_column_pos_of_rank_one_pair {n : ℕ} {Y : Square n}
    (hY : NonnegativeEntries Y) (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (rows : Fin 3 → Fin n) (hr : StrictMono rows)
    {a b q c : Fin n} (hab : a < b) (hbc : b < c)
    (haq : a < q) (hqc : q < c) (hbq : b ≠ q)
    (hpair : (Y.submatrix rows ![q, b]).rank ≤ 1)
    (hbad : Matrix.det (Y.submatrix rows ![a, q, c]) < 0) :
    ∀ r, 0 < Y (rows r) b := by
  have hc : StrictMono ![a, q, c] :=
    (strictMono_vecEmpty.vecCons hqc).vecCons haq
  have hq := middle_column_pos_of_three_minor_neg hY h₂ hr hc hbad
  change ∀ r, 0 < Y (rows r) q at hq
  have hdiag := diagonal_pos_of_nonsingular hY h₂ hdet
  intro r
  by_contra h
  have hrb : Y (rows r) b = 0 := le_antisymm (le_of_not_gt h) (hY _ _)
  have hzero : ∀ s, Y (rows s) b = 0 := by
    intro s
    have hcross := two_cross_zero_of_rank_le_one (Y.submatrix rows ![q, b])
      hpair r s 0 1
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hcross
    rw [hrb] at hcross
    have hp : Y (rows r) q * Y (rows s) b = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt (hq r))
  rcases lt_or_gt_of_ne hbq with hbq | hqb
  · have houter := zero_column_left_of_zero_column_of_pos_right
      hY h₂ hdiag rows hab.le hbq hzero hq
    have hd : Matrix.det (Y.submatrix rows ![a, q, c]) = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero 0 (by intro s; simpa using houter s)
    linarith
  · have houter := zero_column_right_of_zero_column_of_pos_left
      hY h₂ hdiag rows hqb hbc.le hzero hq
    have hd : Matrix.det (Y.submatrix rows ![a, q, c]) = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero 2 (by intro s; simpa using houter s)
    linarith

theorem positive_anchor_common_outer_rank {n : ℕ} {A B : Square n} {η : ℝ}
    (hA₂ : TP2 A) (hB₂ : TP2 B)
    (hAdet : Matrix.det A ≠ 0) (hBdet : Matrix.det B ≠ 0)
    (hA₃ : SignedThreeMinors η A) (hB₃ : SignedThreeMinors η B)
    (hη : η = 1 ∨ η = -1) (rows : Fin 3 → Fin n) (hr : StrictMono rows)
    {a k q l c : Fin n} (hak : a < k) (hkl : k < l)
    (hkq : k ≤ q) (hql : q ≤ l) (hlc : l < c)
    (hAk : ∀ r, 0 < A (rows r) k) (hAl : ∀ r, 0 < A (rows r) l)
    (hBk : ∀ r, 0 < B (rows r) k) (hBl : ∀ r, 0 < B (rows r) l)
    (hAzero : A (rows 0) k * A (rows 2) l - A (rows 0) l * A (rows 2) k = 0)
    (hBzero : B (rows 0) k * B (rows 2) l - B (rows 0) l * B (rows 2) k = 0) :
    ∃ d, (d = a ∨ d = c) ∧
      (A.submatrix rows ![q, d]).rank ≤ 1 ∧ (B.submatrix rows ![q, d]).rank ≤ 1 := by
  have hij : rows 0 < rows 2 := hr (by decide)
  have hAc := rankOneCorner_of_positive_zero_two hA₂ hAdet hA₃ hη hij hkl
    (hAk 0) (hAl 0) (hAk 2) hAzero
  have hBc := rankOneCorner_of_positive_zero_two hB₂ hBdet hB₃ hη hij hkl
    (hBk 0) (hBl 0) (hBk 2) hBzero
  have hcommon := common_corner_orientation hAdet hBdet hη hij hkl hAc hBc
  obtain ⟨d, hd, hAf, hBf⟩ := common_outer_column_of_common_corner hη hak hkq hql hlc hcommon
  refine ⟨d, hd, ?_, ?_⟩
  all_goals
    apply RankOneOn.submatrix_rank_le_one (by assumption)
    · intro r
      exact ⟨hr.monotone (Fin.zero_le r), hr.monotone (Fin.le_last r)⟩
    · intro t
      fin_cases t <;> simp

/-- The normalized fixed-rectangle step: a shared rank-one interior pair
at the two endpoints extends to the same one of the two outer columns. -/
theorem fixed_pair_common_outer_rank {n : ℕ} {A B M : Square n} {η : ℝ}
    (hA : NonnegativeEntries A) (_hB : NonnegativeEntries B) (hM : NonnegativeEntries M)
    (hA₂ : TP2 A) (hB₂ : TP2 B) (hM₂ : TP2 M)
    (hAdet : Matrix.det A ≠ 0) (hBdet : Matrix.det B ≠ 0) (hMdet : Matrix.det M ≠ 0)
    (hA₃ : SignedThreeMinors η A) (hB₃ : SignedThreeMinors η B)
    (hη : η = 1 ∨ η = -1) (rows : Fin 3 → Fin n) (hr : StrictMono rows)
    {a b q c : Fin n} (hab : a < b) (hbc : b < c)
    (haq : a < q) (hqc : q < c) (hbq : b ≠ q)
    (hpair : (M.submatrix rows ![q, b]).rank ≤ 1)
    (hfixA : ∀ r t, t = q ∨ t = b → A (rows r) t = M (rows r) t)
    (hfixB : ∀ r t, t = q ∨ t = b → B (rows r) t = M (rows r) t)
    (hbad : η * Matrix.det (M.submatrix rows ![a, q, c]) < 0) :
    ∃ d, (d = a ∨ d = c) ∧
      (A.submatrix rows ![q, d]).rank ≤ 1 ∧ (B.submatrix rows ![q, d]).rank ≤ 1 := by
  have hpos : (∀ r, 0 < M (rows r) q) ∧ (∀ r, 0 < M (rows r) b) := by
    rcases hη with hη | hη
    · have hneg : Matrix.det (M.submatrix rows ![a, q, c]) < 0 := by
        simpa only [hη, one_mul] using hbad
      have hcols : StrictMono ![a, q, c] :=
        (strictMono_vecEmpty.vecCons hqc).vecCons haq
      exact ⟨middle_column_pos_of_three_minor_neg hM hM₂ hr hcols hneg,
        interior_column_pos_of_rank_one_pair hM hM₂ hMdet rows hr
          hab hbc haq hqc hbq hpair hneg⟩
    · have hneg₃ : NonpositiveThreeMinors A := by
        intro r s hr hs
        have h := hA₃ r s hr hs
        rw [hη] at h
        linarith
      have hq := column_pos_of_between hA hA₂ hAdet hneg₃ haq hqc
      have hb := column_pos_of_between hA hA₂ hAdet hneg₃ hab hbc
      constructor
      · intro r
        rw [← hfixA r q (Or.inl rfl)]
        exact hq (rows r)
      · intro r
        rw [← hfixA r b (Or.inr rfl)]
        exact hb (rows r)
  have hAq : ∀ r, 0 < A (rows r) q := by
    intro r
    rw [hfixA r q (Or.inl rfl)]
    exact hpos.1 r
  have hAb : ∀ r, 0 < A (rows r) b := by
    intro r
    rw [hfixA r b (Or.inr rfl)]
    exact hpos.2 r
  have hBq : ∀ r, 0 < B (rows r) q := by
    intro r
    rw [hfixB r q (Or.inl rfl)]
    exact hpos.1 r
  have hBb : ∀ r, 0 < B (rows r) b := by
    intro r
    rw [hfixB r b (Or.inr rfl)]
    exact hpos.2 r
  have heqA : A.submatrix rows ![q, b] = M.submatrix rows ![q, b] := by
    ext r t
    fin_cases t
    · exact hfixA r q (Or.inl rfl)
    · exact hfixA r b (Or.inr rfl)
  have heqB : B.submatrix rows ![q, b] = M.submatrix rows ![q, b] := by
    ext r t
    fin_cases t
    · exact hfixB r q (Or.inl rfl)
    · exact hfixB r b (Or.inr rfl)
  have hpairA : (A.submatrix rows ![q, b]).rank ≤ 1 := by rw [heqA]; exact hpair
  have hpairB : (B.submatrix rows ![q, b]).rank ≤ 1 := by rw [heqB]; exact hpair
  rcases lt_or_gt_of_ne hbq with hbq | hqb
  · have hAzero := two_cross_zero_of_rank_le_one (A.submatrix rows ![q, b]) hpairA 0 2 1 0
    have hBzero := two_cross_zero_of_rank_le_one (B.submatrix rows ![q, b]) hpairB 0 2 1 0
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hAzero hBzero
    exact positive_anchor_common_outer_rank hA₂ hB₂ hAdet hBdet hA₃ hB₃ hη rows hr
      hab hbq hbq.le le_rfl hqc hAb hAq hBb hBq hAzero hBzero
  · have hAzero := two_cross_zero_of_rank_le_one (A.submatrix rows ![q, b]) hpairA 0 2 0 1
    have hBzero := two_cross_zero_of_rank_le_one (B.submatrix rows ![q, b]) hpairB 0 2 0 1
    simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hAzero hBzero
    exact positive_anchor_common_outer_rank hA₂ hB₂ hAdet hBdet hA₃ hB₃ hη rows hr
      haq hqb le_rfl hqb.le hbc hAq hAb hBq hBb hAzero hBzero

/-- Lift an at-most-one normalized Schur rank through the original pivot.
This uses the same selected row order as the normalized three-minor. -/
theorem source_rank_le_pivot_add_one_of_normalized_rank_le_one
    {n p m r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m)
    (hH : (M.submatrix P Q).det ≠ 0) (ha : e * e₁ ≠ 0)
    (hrank : ((normalizedSchur M P Q R C e e₁ e₂).submatrix
      (orientedRows rows e e₂) cols).rank ≤ 1) :
    (M.submatrix (appendIndices P (R ∘ rows))
      (appendIndices Q (C ∘ cols))).rank ≤ p + 1 := by
  rw [schurAt_rank M P Q (R ∘ rows) (C ∘ cols) hH]
  rw [normalizedSchur_submatrix_rank M P Q R C e e₁ e₂ rows cols ha] at hrank
  omega

/-- The reverse rank implication supplies the rank-one interior Schur
block from the permanent interior-rectangle rank bound. -/
theorem normalized_rank_le_one_of_source_rank_le_pivot_add_one
    {n p m r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m)
    (hH : (M.submatrix P Q).det ≠ 0) (ha : e * e₁ ≠ 0)
    (hrank : (M.submatrix (appendIndices P (R ∘ rows))
      (appendIndices Q (C ∘ cols))).rank ≤ p + 1) :
    ((normalizedSchur M P Q R C e e₁ e₂).submatrix
      (orientedRows rows e e₂) cols).rank ≤ 1 := by
  rw [schurAt_rank M P Q (R ∘ rows) (C ∘ cols) hH] at hrank
  rw [normalizedSchur_submatrix_rank M P Q R C e e₁ e₂ rows cols ha]
  omega

/-- Only the four pivot/residual blocks determine a selected Schur block. -/
theorem signedSchurAt_eq_of_blocks_eq {n p r c : ℕ} {A B : Square n}
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (hPQ : A.submatrix P Q = B.submatrix P Q)
    (hRQ : A.submatrix R Q = B.submatrix R Q)
    (hPC : A.submatrix P C = B.submatrix P C)
    (hRC : A.submatrix R C = B.submatrix R C) :
    signedSchurAt A P Q R C = signedSchurAt B P Q R C := by
  simp only [signedSchurAt, schurAt, hPQ, hRQ, hPC, hRC]

/-- A fixed source rectangle gives an identical selected normalized Schur
block, including when normalization reverses the selected row order. -/
theorem normalizedSchur_block_eq_of_blocks_eq {n p m r c : ℕ} {A B : Square n}
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m)
    (hPQ : A.submatrix P Q = B.submatrix P Q)
    (hRQ : A.submatrix (R ∘ rows) Q = B.submatrix (R ∘ rows) Q)
    (hPC : A.submatrix P (C ∘ cols) = B.submatrix P (C ∘ cols))
    (hRC : A.submatrix (R ∘ rows) (C ∘ cols) =
      B.submatrix (R ∘ rows) (C ∘ cols)) :
    (normalizedSchur A P Q R C e e₁ e₂).submatrix (orientedRows rows e e₂) cols =
      (normalizedSchur B P Q R C e e₁ e₂).submatrix (orientedRows rows e e₂) cols := by
  rw [normalizedSchur_submatrix, normalizedSchur_submatrix]
  rw [signedSchurAt_eq_of_blocks_eq P Q (R ∘ rows) (C ∘ cols) hPQ hRQ hPC hRC]

/-- The same lift when the original rectangle is supplied in any fixed
sorted order, using explicit sorting permutations. -/
theorem sorted_source_rank_le_pivot_add_one_of_normalized_rank_le_one
    {n p m r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (rows : Fin r → Fin m) (cols : Fin c → Fin m)
    (Rall : Fin (p + r) → Fin n) (Call : Fin (p + c) → Fin n)
    (σ : Equiv.Perm (Fin (p + r))) (τ : Equiv.Perm (Fin (p + c)))
    (hsortR : appendIndices P (R ∘ rows) = Rall ∘ σ)
    (hsortC : appendIndices Q (C ∘ cols) = Call ∘ τ)
    (hH : (M.submatrix P Q).det ≠ 0) (ha : e * e₁ ≠ 0)
    (hrank : ((normalizedSchur M P Q R C e e₁ e₂).submatrix
      (orientedRows rows e e₂) cols).rank ≤ 1) :
    (M.submatrix Rall Call).rank ≤ p + 1 := by
  rw [schurAt_sorted_rank M P Q (R ∘ rows) (C ∘ cols) Rall Call σ τ hsortR hsortC hH]
  rw [normalizedSchur_submatrix_rank M P Q R C e e₁ e₂ rows cols ha] at hrank
  omega

/-- If a rectangle has only one possibly variable column, common endpoint
rank bounds persist throughout the box once the next-order signs hold. -/
theorem fixed_except_one_column_rank_bound_on_box {n r a b : ℕ}
    {L U : Square n} (hLU : EntrywiseLE L U)
    (R : Fin a → Fin n) (C : Fin b → Fin n)
    (hR : StrictMono R) (hC : StrictMono C) (d : Fin b)
    (hfixed : ∀ i j, j ≠ d → L (R i) (C j) = U (R i) (C j))
    (s : ℝ) (hs : s ≠ 0)
    (hnonneg : ∀ X, InBox L U X → HasSignedMinors X (r + 1) s)
    (hminus : ((checkerMinus L U).submatrix R C).rank ≤ r)
    (hplus : ((checkerPlus L U).submatrix R C).rank ≤ r)
    {X : Square n} (hX : InBox L U X) : (X.submatrix R C).rank ≤ r := by
  apply (rank_le_iff_all_increasing_minors_zero _ r).mpr
  intro rows cols hr hc
  have hmzero := (rank_le_iff_all_increasing_minors_zero _ r).mp hminus rows cols hr hc
  have hpzero := (rank_le_iff_all_increasing_minors_zero _ r).mp hplus rows cols hr hc
  change minor (checkerMinus L U) (R ∘ rows) (C ∘ cols) = 0 at hmzero
  change minor (checkerPlus L U) (R ∘ rows) (C ∘ cols) = 0 at hpzero
  change minor X (R ∘ rows) (C ∘ cols) = 0
  have hsign : ∀ M, InBox L U M →
      0 ≤ s * minor M (R ∘ rows) (C ∘ cols) :=
    fun M hM => hnonneg M hM _ _ (hR.comp hr) (hC.comp hc)
  by_cases hex : ∃ j, cols j = d
  · obtain ⟨j, hj⟩ := hex
    apply fixed_columns_minor_zero_on_box hLU (R ∘ rows) (C ∘ cols)
      (hR.comp hr) (hC.comp hc) j _ s hs hsign hmzero hpzero hX
    intro i t ht
    apply hfixed (rows i) (cols t)
    intro heq
    exact ht (hc.injective (heq.trans hj.symm))
  · apply fixed_columns_minor_zero_on_box hLU (R ∘ rows) (C ∘ cols)
      (hR.comp hr) (hC.comp hc) 0 _ s hs hsign hmzero hpzero hX
    intro i t _
    exact hfixed (rows i) (cols t) (fun h => hex ⟨t, h⟩)

/-- Rank at most `r` after deleting one column of an `(r+2)`-square matrix
forces its determinant to vanish. -/
theorem det_zero_of_deleted_column_rank_le {r : ℕ} (Y : Square (r + 2))
    (cols : Fin (r + 1) → Fin (r + 2)) (hc : Function.Injective cols)
    (hrank : (Y.submatrix id cols).rank ≤ r) : Y.det = 0 := by
  by_contra hd
  have hsize := Matrix.rank_of_det_ne_zero hd
  have hbound := rank_add_card_le_rank_submatrix_cols_add_card Y cols hc
  simp only [hsize, Fintype.card_fin] at hbound
  omega

/-- The final midpoint contradiction of Section 7.1, once the common
endpoint extension rank bound has been lifted from Schur complements. -/
theorem fixed_endpoint_extension_forces_target_zero {n r : ℕ}
    {L U : Square n} (hLU : EntrywiseLE L U)
    (R J : Fin (r + 2) → Fin n) (hR : StrictMono R) (hJ : StrictMono J)
    (cols : Fin (r + 1) → Fin (r + 2)) (hc : StrictMono cols) (d : Fin (r + 1))
    (hfixed : ∀ i j, j ≠ d → L (R i) (J (cols j)) = U (R i) (J (cols j)))
    (s : ℝ) (hs : s ≠ 0)
    (hnonneg : ∀ X, InBox L U X → HasSignedMinors X (r + 1) s)
    (hminus : ((checkerMinus L U).submatrix R (J ∘ cols)).rank ≤ r)
    (hplus : ((checkerPlus L U).submatrix R (J ∘ cols)).rank ≤ r)
    {X : Square n} (hX : InBox L U X) : minor X R J = 0 := by
  have hrank := fixed_except_one_column_rank_bound_on_box hLU R (J ∘ cols)
    hR (hJ.comp hc) d hfixed s hs hnonneg hminus hplus hX
  exact det_zero_of_deleted_column_rank_le (X.submatrix R J) cols hc.injective hrank

end IV01
