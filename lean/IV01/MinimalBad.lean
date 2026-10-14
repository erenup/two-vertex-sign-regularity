import IV01.RankMinors
import IV01.FeketeIdentity
import IV01.InteriorZero
import IV01.SolidMinors
import IV01.EssentialRank
import IV01.IndexSelection
import IV01.Transpose

namespace IV01

open Matrix

/-- The sign consequence of Fekete's identity: a bad large minor and two
correct smaller-span minors force the middle lower minor to vanish. -/
theorem fekete_denominator_zero_of_bad
    {D Dl Dr d dl dr σ η : ℝ} (hη : η ≠ 0)
    (hidentity : D * d = Dl * dl + Dr * dr)
    (hbad : σ * D < 0) (hl : 0 ≤ σ * Dl) (hr : 0 ≤ σ * Dr)
    (hd : 0 ≤ η * d) (hdl : 0 ≤ η * dl) (hdr : 0 ≤ η * dr) : d = 0 := by
  have hmul : (σ * D) * (η * d) = (σ * Dl) * (η * dl) + (σ * Dr) * (η * dr) := by
    linear_combination σ * η * hidentity
  have hnonneg : 0 ≤ (σ * D) * (η * d) := by
    rw [hmul]
    exact add_nonneg (mul_nonneg hl hdl) (mul_nonneg hr hdr)
  have hnonpos : η * d ≤ 0 := nonpos_of_mul_nonneg_right hnonneg hbad
  exact (mul_eq_zero.mp (le_antisymm hnonpos hd)).resolve_left hη

/-- The pure finite-matrix rank reduction underlying Section 5.3. In a sorted
union of `q+3` columns, suppose deleting one interior column gives a bad
`q+2` minor, whereas deleting either extreme column gives a correct minor.
If all lower minors have the common nonzero sign, the interior block has
rank at most `q`. -/
theorem rank_interior_le_of_bad_middle {q : ℕ}
    (A : Matrix (Fin (q + 2)) (Fin (q + 3)) ℝ) (b : Fin (q + 1))
    (σ η : ℝ) (hη : η ≠ 0)
    (hlower : ∀ rows : Fin (q + 1) → Fin (q + 2),
      ∀ cols : Fin (q + 1) → Fin (q + 3),
      StrictMono rows → StrictMono cols → 0 ≤ η * (A.submatrix rows cols).det)
    (hbad : σ * (A.submatrix id (feketeInterior b).succAbove).det < 0)
    (hleft : 0 ≤ σ * (A.submatrix id Fin.succ).det)
    (hright : 0 ≤ σ * (A.submatrix id Fin.castSucc).det) :
    (A.submatrix id feketeInterior).rank ≤ q := by
  rw [rank_le_iff_all_increasing_minors_zero]
  intro rows cols hrows hcols
  have hcolsId : cols = id := hcols.eq_id
  subst cols
  simp only [Matrix.submatrix_submatrix, Function.id_comp, Function.comp_id]
  exact fekete_denominator_zero_of_bad hη (fekete_three_term A rows b) hbad hleft hright
    (hlower rows feketeInterior hrows strictMono_feketeInterior)
    (hlower rows (feketeLeft b) hrows (strictMono_feketeLeft b))
    (hlower rows (feketeRight b) hrows (strictMono_feketeRight b))

/-- A rectangular rank bound at a relative-interior point is permanent whenever
all minors of the next order have a common prescribed nonzero sign on the box. -/
theorem rectangle_rank_bound_on_box
    {n r : ℕ} {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    {L U M : Square n} (rows : α → Fin n) (cols : β → Fin n)
    (hr : StrictMono rows) (hc : StrictMono cols) (s : ℝ) (hs : s ≠ 0)
    (hnonneg : ∀ X, InBox L U X → ∀ a b : Fin (r + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ s * minor X a b)
    (hM : InRelativeInterior L U M) (hrank : (M.submatrix rows cols).rank ≤ r)
    {X : Square n} (hX : InBox L U X) : (X.submatrix rows cols).rank ≤ r := by
  rw [rank_le_iff_all_increasing_minors_zero]
  intro a b ha hb
  have hzero : minor M (rows ∘ a) (cols ∘ b) = 0 := by
    have hz := (rank_le_iff_all_increasing_minors_zero (M.submatrix rows cols) r).mp hrank
      a b ha hb
    simpa only [Matrix.submatrix_submatrix, minor] using hz
  have hz := minor_zero_on_box (rows ∘ a) (cols ∘ b) (hr.comp ha) (hc.comp hb) s hs
    (fun Y hY => hnonneg Y hY _ _ (hr.comp ha) (hc.comp hb)) hM hzero hX
  simpa only [Matrix.submatrix_submatrix, minor] using hz

/-- A genuinely variable entry of a rectangle whose rank is maximal at the
relative-interior matrix lies in an essential row or an essential column. -/
theorem essential_line_of_free_entry
    {n : ℕ} {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {L U M : Square n} (rows : α → Fin n) (cols : β → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hM : InRelativeInterior L U M)
    (hbound : ∀ X, InBox L U X → (X.submatrix rows cols).rank ≤ (M.submatrix rows cols).rank)
    (i : α) (j : β) (hfree : L (rows i) (cols j) < U (rows i) (cols j)) :
    ((M.submatrix rows cols).submatrix (Subtype.val : {a : α // a ≠ i} → α) id).rank + 1 =
        (M.submatrix rows cols).rank ∨
      ((M.submatrix rows cols).submatrix id (Subtype.val : {b : β // b ≠ j} → β)).rank + 1 =
        (M.submatrix rows cols).rank := by
  let t := (U (rows i) (cols j) - M (rows i) (cols j)) / 2
  have hpos : 0 < t := by
    dsimp [t]
    exact div_pos (sub_pos.mpr (hM.2 _ _ hfree).2) (by norm_num)
  let X : Square n := M + Matrix.single (rows i) (cols j) t
  have hX : InBox L U X := by
    constructor <;> intro a b
    · by_cases ha : a = rows i
      · subst a
        by_cases hb : b = cols j
        · subst b
          simp only [X, Matrix.add_apply, Matrix.single_apply_same]
          have h := hM.1.1 (rows i) (cols j)
          linarith
        · simpa [X, Matrix.single_apply, Ne.symm hb] using hM.1.1 (rows i) b
      · simpa [X, Matrix.single_apply, Ne.symm ha] using hM.1.1 a b
    · by_cases ha : a = rows i
      · subst a
        by_cases hb : b = cols j
        · subst b
          simp only [X, Matrix.add_apply, Matrix.single_apply_same]
          have h := hM.1.2 (rows i) (cols j)
          dsimp [t]
          linarith
        · simpa [X, Matrix.single_apply, Ne.symm hb] using hM.1.2 (rows i) b
      · simpa [X, Matrix.single_apply, Ne.symm ha] using hM.1.2 a b
  have hsub : X.submatrix rows cols = M.submatrix rows cols + Matrix.single i j t := by
    ext a b
    simp only [X, Matrix.submatrix_apply, Matrix.add_apply, Matrix.single_apply,
      hr.eq_iff, hc.eq_iff]
  apply essential_row_or_column_of_rank_single (M.submatrix rows cols) i j t hpos.ne'
  rw [← hsub]
  exact hbound X hX

/-- The rank of the full open interior column rectangle of a column-span-minimal
bad minor is exactly two less than the order of the bad minor. -/
theorem rank_interior_eq_of_minimal_bad {n q : ℕ}
    (M : Square n) (rows cols : Fin (q + 2) → Fin n)
    (hr : StrictMono rows) (hc : StrictMono cols) (σ η : ℝ) (hη : η ≠ 0)
    (hlower : ∀ a b : Fin (q + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ η * minor M a b)
    (hbad : σ * minor M rows cols < 0)
    (hsmaller : ∀ c : Fin (q + 2) → Fin n, StrictMono c →
      indexSpan c < indexSpan cols → 0 ≤ σ * minor M rows c) :
    (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = q := by
  classical
  let core : Fin q → Fin n := cols ∘ middleIndices
  let C : Matrix (Fin (q + 2)) (Fin q) ℝ := M.submatrix rows core
  let P := columnSpace C
  have hdet : (M.submatrix rows cols).det ≠ 0 := by
    intro hz
    have hz' : minor M rows cols = 0 := hz
    rw [hz', mul_zero] at hbad
    exact (lt_irrefl 0) hbad
  have hli := (Matrix.linearIndependent_cols_of_det_ne_zero hdet).comp
    middleIndices strictMono_middleIndices.injective
  have hrankC : C.rank = q := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have hh := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Module.finrank ℝ (Submodule.span ℝ (Set.range ((M.submatrix rows cols).col ∘ middleIndices))) = q
    simpa only [Set.finrank, Fintype.card_fin] using hh.symm
  have hPdim : Module.finrank ℝ P = q := by
    rw [← rank_eq_finrank_columnSpace C]
    exact hrankC
  have hmem (c : InteriorColumns cols) : (fun a => M (rows a) c.val) ∈ P := by
    by_cases hcin : c.val ∈ Set.range cols
    · obtain ⟨j, hj⟩ := (mem_range_middle_iff cols hc c.val).mpr ⟨hcin, c.property⟩
      have hcol := col_mem_columnSpace C j
      change (fun a => M (rows a) (cols (middleIndices j))) ∈ P at hcol
      change cols (middleIndices j) = c.val at hj
      rw [hj] at hcol
      exact hcol
    · obtain ⟨all, b, hall, hb, hdelete, h0, hl⟩ :=
        exists_sorted_interior_insertion cols hc c.val c.property.1 c.property.2 hcin
      let B := M.submatrix rows all
      have hBlower : ∀ a : Fin (q + 1) → Fin (q + 2),
          ∀ d : Fin (q + 1) → Fin (q + 3), StrictMono a → StrictMono d →
          0 ≤ η * (B.submatrix a d).det := by
        intro a d ha hd
        exact hlower (rows ∘ a) (all ∘ d) (hr.comp ha) (hall.comp hd)
      have hBbad : σ * (B.submatrix id (feketeInterior b).succAbove).det < 0 := by
        simpa only [B, Matrix.submatrix_submatrix, Function.comp_id, hdelete, minor] using hbad
      have hBleft : 0 ≤ σ * (B.submatrix id Fin.succ).det := by
        exact hsmaller (all ∘ Fin.succ) (hall.comp Fin.strictMono_succ)
          (indexSpan_drop_first_lt all hall cols h0 hl)
      have hBright : 0 ≤ σ * (B.submatrix id Fin.castSucc).det := by
        exact hsmaller (all ∘ Fin.castSucc) (hall.comp Fin.strictMono_castSucc)
          (indexSpan_drop_last_lt all hall cols h0 hl)
      have hBrank := rank_interior_le_of_bad_middle B b σ η hη hBlower hBbad hBleft hBright
      let Q := columnSpace (B.submatrix id feketeInterior)
      have hPQ : P ≤ Q := by
        apply Submodule.span_le.mpr
        rintro v ⟨j, rfl⟩
        have hJ : cols (middleIndices j) ∈ Set.range all := by
          refine ⟨(feketeInterior b).succAbove (middleIndices j), ?_⟩
          exact congrFun hdelete (middleIndices j)
        have hbetween : all 0 < cols (middleIndices j) ∧
            cols (middleIndices j) < all (Fin.last (q + 2)) := by
          rw [h0, hl]
          exact ⟨hc (middleIndices_pos j), hc (middleIndices_lt_last j)⟩
        obtain ⟨z, hz⟩ := (mem_range_middle_iff all hall (cols (middleIndices j))).mpr
          ⟨hJ, hbetween⟩
        have hcol := col_mem_columnSpace (B.submatrix id feketeInterior) z
        change (fun a => M (rows a) (all (feketeInterior z))) ∈ Q at hcol
        change all (feketeInterior z) = cols (middleIndices j) at hz
        change (fun a => M (rows a) (cols (middleIndices j))) ∈ Q
        simpa only [hz] using hcol
      have hQdim : Module.finrank ℝ Q ≤ Module.finrank ℝ P := by
        rw [hPdim, ← rank_eq_finrank_columnSpace (B.submatrix id feketeInterior)]
        exact hBrank
      have heq : P = Q := Submodule.eq_of_le_of_finrank_le hPQ hQdim
      rw [heq]
      have hcol := col_mem_columnSpace (B.submatrix id feketeInterior) b
      change (fun a => M (rows a) (all (feketeInterior b))) ∈ Q at hcol
      simpa only [hb] using hcol
  have hupper : (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ q := by
    rw [rank_eq_finrank_columnSpace]
    calc
      _ ≤ Module.finrank ℝ P := by
        apply Submodule.finrank_mono
        apply Submodule.span_le.mpr
        rintro v ⟨c, rfl⟩
        exact hmem c
      _ = q := hPdim
  have hlowerRank := (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank_submatrix_le
    id (coreToInterior cols hc)
  have hsub : (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).submatrix
      id (coreToInterior cols hc) = C := rfl
  rw [hsub, hrankC] at hlowerRank
  exact le_antisymm hupper hlowerRank

/-- Choose a bad minor minimizing the sum of its row and column spans. -/
theorem exists_minimal_bad_minor {n q : ℕ} (M : Square n) (σ : ℝ)
    (hbad : ∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0) :
    ∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0 ∧
      ∀ r c : Fin (q + 2) → Fin n, StrictMono r → StrictMono c →
        σ * minor M r c < 0 → indexSpan rows + indexSpan cols ≤ indexSpan r + indexSpan c := by
  classical
  have hex : ∃ s : ℕ, ∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0 ∧
        indexSpan rows + indexSpan cols = s := by
    obtain ⟨rows, cols, hr, hc, hb⟩ := hbad
    exact ⟨_, rows, cols, hr, hc, hb, rfl⟩
  obtain ⟨rows, cols, hr, hc, hb, hs⟩ := Nat.find_spec hex
  refine ⟨rows, cols, hr, hc, hb, fun r c hr hc hbad => ?_⟩
  rw [hs]
  exact Nat.find_min' hex ⟨r, c, hr, hc, hbad, rfl⟩

/-- The complete fixed-matrix minimal-bad-minor reduction. A gap is oriented
into the column direction, by transposing the matrix when necessary. -/
theorem exists_bad_rectangle_or_transpose {n q : ℕ}
    (M : Square n) (σ η : ℝ) (hη : η ≠ 0)
    (hlower : ∀ a b : Fin (q + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ η * minor M a b)
    (hsolid : ∀ (a b : ℕ) (ha : a + (q + 2) ≤ n) (hb : b + (q + 2) ≤ n),
      0 ≤ σ * minor M (consecutiveIndices n (q + 2) a ha)
        (consecutiveIndices n (q + 2) b hb))
    (hbad : ∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0) :
    (∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0 ∧
      q + 1 ≤ Fintype.card (InteriorColumns cols) ∧
      (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = q) ∨
    (∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor Mᵀ rows cols < 0 ∧
      q + 1 ≤ Fintype.card (InteriorColumns cols) ∧
      (Mᵀ.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = q) := by
  obtain ⟨rows, cols, hr, hc, hb, hmin⟩ := exists_minimal_bad_minor M σ hbad
  have hsmallerC : ∀ c : Fin (q + 2) → Fin n, StrictMono c →
      indexSpan c < indexSpan cols → 0 ≤ σ * minor M rows c := by
    intro c hc' hs
    by_contra hneg
    have h := hmin rows c hr hc' (lt_of_not_ge hneg)
    omega
  rcases consecutive_or_gap cols hc with ⟨b, hbn, hcols⟩ | hgap
  · rcases consecutive_or_gap rows hr with ⟨a, han, hrows⟩ | hgap
    · have h := hsolid a b han hbn
      rw [← hrows, ← hcols] at h
      exact False.elim (not_lt_of_ge h hb)
    · right
      have hbT : σ * minor Mᵀ cols rows < 0 := by simpa only [minor_transpose] using hb
      have hlowerT : ∀ a b : Fin (q + 1) → Fin n,
          StrictMono a → StrictMono b → 0 ≤ η * minor Mᵀ a b := by
        intro a b ha hb
        rw [minor_transpose]
        exact hlower b a hb ha
      have hsmallerR : ∀ r : Fin (q + 2) → Fin n, StrictMono r →
          indexSpan r < indexSpan rows → 0 ≤ σ * minor Mᵀ cols r := by
        intro r hr' hs
        rw [minor_transpose]
        by_contra hneg
        have h := hmin r cols hr' hc (lt_of_not_ge hneg)
        omega
      exact ⟨cols, rows, hc, hr, hbT, card_interior_ge_of_gap rows hr hgap,
        rank_interior_eq_of_minimal_bad Mᵀ cols rows hc hr σ η hη hlowerT hbT hsmallerR⟩
  · left
    exact ⟨rows, cols, hr, hc, hb, card_interior_ge_of_gap cols hc hgap,
      rank_interior_eq_of_minimal_bad M rows cols hr hc σ η hη hlower hb hsmallerC⟩

/-- The minimal bad rectangle certificate including its permanent rank bound
on the entire box, with an explicit alternative for transposed data. -/
theorem exists_permanent_bad_rectangle_or_transpose {n q : ℕ}
    {L U M : Square n} (σ η : ℝ) (hη : η ≠ 0)
    (hM : InRelativeInterior L U M)
    (hlower : ∀ X, InBox L U X → ∀ a b : Fin (q + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ η * minor X a b)
    (hsolid : ∀ (a b : ℕ) (ha : a + (q + 2) ≤ n) (hb : b + (q + 2) ≤ n),
      0 ≤ σ * minor M (consecutiveIndices n (q + 2) a ha)
        (consecutiveIndices n (q + 2) b hb))
    (hbad : ∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0) :
    (∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor M rows cols < 0 ∧
      q + 1 ≤ Fintype.card (InteriorColumns cols) ∧
      (M.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = q ∧
      ∀ X, InBox L U X → (X.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ q) ∨
    (∃ rows cols : Fin (q + 2) → Fin n,
      StrictMono rows ∧ StrictMono cols ∧ σ * minor Mᵀ rows cols < 0 ∧
      q + 1 ≤ Fintype.card (InteriorColumns cols) ∧
      (Mᵀ.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank = q ∧
      ∀ X, InBox Lᵀ Uᵀ X → (X.submatrix rows (Subtype.val : InteriorColumns cols → Fin n)).rank ≤ q) := by
  rcases exists_bad_rectangle_or_transpose M σ η hη (hlower M hM.1) hsolid hbad with
    ⟨rows, cols, hr, hc, hb, hcard, hrank⟩ | ⟨rows, cols, hr, hc, hb, hcard, hrank⟩
  · left
    refine ⟨rows, cols, hr, hc, hb, hcard, hrank, fun X hX => ?_⟩
    exact rectangle_rank_bound_on_box rows (Subtype.val : InteriorColumns cols → Fin n)
      hr (fun _ _ h => h) η hη hlower hM hrank.le hX
  · right
    refine ⟨rows, cols, hr, hc, hb, hcard, hrank, fun X hX => ?_⟩
    apply rectangle_rank_bound_on_box rows (Subtype.val : InteriorColumns cols → Fin n)
      hr (fun _ _ h => h) η hη ?_ hM.transpose hrank.le hX
    intro Y hY a b ha hb
    have hYT : InBox L U Yᵀ := by
      simpa only [Matrix.transpose_transpose] using hY.transpose
    simpa only [minor_transpose] using hlower Yᵀ hYT b a hb ha

/-- Section 5.4 with the subsequent permanence step included: deleting an
essential line lowers the interior rank by one and bounds that residual rank
at every matrix in the box. -/
theorem essential_residual_rank_on_box
    {n p : ℕ} {α β : Type*} [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]
    {L U M : Square n} (rows : α → Fin n) (cols : β → Fin n)
    (hr : StrictMono rows) (hc : StrictMono cols)
    (hM : InRelativeInterior L U M)
    (hrank : (M.submatrix rows cols).rank = p + 1)
    (hbound : ∀ X, InBox L U X → (X.submatrix rows cols).rank ≤ p + 1)
    (η : ℝ) (hη : η ≠ 0)
    (hlower : ∀ X, InBox L U X → ∀ a b : Fin (p + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ η * minor X a b)
    (i : α) (j : β) (hfree : L (rows i) (cols j) < U (rows i) (cols j)) :
    ((M.submatrix (rows ∘ (Subtype.val : {a : α // a ≠ i} → α)) cols).rank = p ∧
      ∀ X, InBox L U X →
        (X.submatrix (rows ∘ (Subtype.val : {a : α // a ≠ i} → α)) cols).rank ≤ p) ∨
    ((M.submatrix rows (cols ∘ (Subtype.val : {b : β // b ≠ j} → β))).rank = p ∧
      ∀ X, InBox L U X →
        (X.submatrix rows (cols ∘ (Subtype.val : {b : β // b ≠ j} → β))).rank ≤ p) := by
  have hbound' : ∀ X, InBox L U X →
      (X.submatrix rows cols).rank ≤ (M.submatrix rows cols).rank := by
    intro X hX
    rw [hrank]
    exact hbound X hX
  rcases essential_line_of_free_entry rows cols hr.injective hc.injective hM hbound' i j hfree with
    hrow | hcol
  · left
    have heq : (M.submatrix (rows ∘ (Subtype.val : {a : α // a ≠ i} → α)) cols).rank = p := by
      simp only [Matrix.submatrix_submatrix, Function.comp_id, hrank, Nat.add_right_cancel_iff] at hrow
      exact hrow
    refine ⟨heq, fun X hX => ?_⟩
    exact rectangle_rank_bound_on_box
      (rows ∘ (Subtype.val : {a : α // a ≠ i} → α)) cols
      (hr.comp (show StrictMono (Subtype.val : {a : α // a ≠ i} → α) from fun _ _ h => h))
      hc η hη hlower hM heq.le hX
  · right
    have heq : (M.submatrix rows (cols ∘ (Subtype.val : {b : β // b ≠ j} → β))).rank = p := by
      simp only [Matrix.submatrix_submatrix, Function.comp_id, hrank, Nat.add_right_cancel_iff] at hcol
      exact hcol
    refine ⟨heq, fun X hX => ?_⟩
    exact rectangle_rank_bound_on_box rows
      (cols ∘ (Subtype.val : {b : β // b ≠ j} → β)) hr
      (hc.comp (show StrictMono (Subtype.val : {b : β // b ≠ j} → β) from fun _ _ h => h))
      η hη hlower hM heq.le hX

end IV01
