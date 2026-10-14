import IV01.Corner
import IV01.RankBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Order.Interval.Finset.Fin

/-!
# Positive zero-two anchors

The normalization is by a column ratio. This leaves zero rows admissible
throughout the determinant identities and avoids dividing by their entries.
-/

namespace IV01

def SignedThreeMinors {ι κ : Type*} [Preorder ι] [Preorder κ]
    (η : ℝ) (Y : Matrix ι κ ℝ) : Prop :=
  ∀ rows : Fin 3 → ι, ∀ cols : Fin 3 → κ,
    StrictMono rows → StrictMono cols →
    0 ≤ η * Matrix.det (Y.submatrix rows cols)

noncomputable def detThree {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (r s h : ι) (k l t : κ) : ℝ :=
  Matrix.det (Y.submatrix ![r, s, h] ![k, l, t])

def rowCross {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (r s : ι) (k t : κ) : ℝ := Y r k * Y s t - Y s k * Y r t

def columnDifference {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (k l : κ) (ρ : ℝ) (r : ι) : ℝ := Y r l - ρ * Y r k

def RankOneOn {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (R : ι → Prop) (C : κ → Prop) : Prop :=
  ∃ u : ι → ℝ, ∃ v : κ → ℝ,
    ∀ r, R r → ∀ c, C c → Y r c = u r * v c

theorem detThree_cyclic_rows {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (r s h : ι) (k l t : κ) :
    detThree Y r s h k l t = detThree Y h r s k l t := by
  unfold detThree
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp
  ring

theorem detThree_cyclic_cols {ι κ : Type*} (Y : Matrix ι κ ℝ)
    (r s h : ι) (k l t : κ) :
    detThree Y r s h k l t = detThree Y r s h t k l := by
  unfold detThree
  rw [Matrix.det_fin_three, Matrix.det_fin_three]
  simp
  ring

theorem detThree_anchor_identity {ι κ : Type*} {Y : Matrix ι κ ℝ}
    {r s h : ι} {k l t : κ} {ρ : ℝ}
    (hr : columnDifference Y k l ρ r = 0)
    (hs : columnDifference Y k l ρ s = 0) :
    detThree Y r s h k l t =
      -(rowCross Y r s k t) * columnDifference Y k l ρ h := by
  have hr' : Y r l = ρ * Y r k := sub_eq_zero.mp hr
  have hs' : Y s l = ρ * Y s k := sub_eq_zero.mp hs
  unfold detThree
  rw [Matrix.det_fin_three]
  simp [hr', hs', rowCross, columnDifference]
  ring

private theorem strictMono_three {ι : Type*} [Preorder ι]
    {a b c : ι} (hab : a < b) (hbc : b < c) : StrictMono ![a, b, c] :=
  (strictMono_vecEmpty.vecCons hbc).vecCons hab

theorem SignedThreeMinors.external {ι κ : Type*}
    [Preorder ι] [Preorder κ] {Y : Matrix ι κ ℝ} {η : ℝ}
    (h₃ : SignedThreeMinors η Y) {r s h : ι} {k l t : κ}
    (hrs : r < s) (hkl : k < l)
    (hh : h < r ∨ s < h) (ht : t < k ∨ l < t) :
    0 ≤ η * detThree Y r s h k l t := by
  rcases hh with hhr | hsh <;> rcases ht with htk | hlt
  · rw [detThree_cyclic_rows Y r s h k l t,
      detThree_cyclic_cols Y h r s k l t]
    exact h₃ _ _ (strictMono_three hhr hrs) (strictMono_three htk hkl)
  · rw [detThree_cyclic_rows Y r s h k l t]
    exact h₃ _ _ (strictMono_three hhr hrs) (strictMono_three hkl hlt)
  · rw [detThree_cyclic_cols Y r s h k l t]
    exact h₃ _ _ (strictMono_three hrs hsh) (strictMono_three htk hkl)
  · exact h₃ _ _ (strictMono_three hrs hsh) (strictMono_three hkl hlt)

section Ordered

variable {ι κ : Type*} [LinearOrder ι] [LinearOrder κ]
variable {Y : Matrix ι κ ℝ}

theorem rowCross_nonneg_of_le (h₂ : TP2 Y) {r s : ι} {k t : κ}
    (hrs : r < s) (hkt : k ≤ t) : 0 ≤ rowCross Y r s k t := by
  rcases eq_or_lt_of_le hkt with rfl | hkt
  · simp [rowCross, mul_comm]
  · simpa only [rowCross, mul_comm] using h₂ r s k t hrs hkt

theorem rowCross_nonpos_of_le (h₂ : TP2 Y) {r s : ι} {k l t : κ} {ρ : ℝ}
    (hrs : r < s) (hρ : 0 < ρ)
    (hr : columnDifference Y k l ρ r = 0)
    (hs : columnDifference Y k l ρ s = 0)
    (htl : t ≤ l) : rowCross Y r s k t ≤ 0 := by
  have hr' : Y r l = ρ * Y r k := sub_eq_zero.mp hr
  have hs' : Y s l = ρ * Y s k := sub_eq_zero.mp hs
  rcases eq_or_lt_of_le htl with rfl | htl
  · simp [rowCross, hr', hs']
    ring_nf
    exact le_rfl
  · have hminor := h₂ r s t l hrs htl
    rw [hr', hs'] at hminor
    by_contra h
    have hprod := mul_pos hρ (lt_of_not_ge h)
    dsimp [rowCross] at hprod
    nlinarith

theorem rowCross_zero_between (h₂ : TP2 Y) {r s : ι} {k l t : κ} {ρ : ℝ}
    (hrs : r < s) (hρ : 0 < ρ)
    (hr : columnDifference Y k l ρ r = 0)
    (hs : columnDifference Y k l ρ s = 0)
    (hkt : k ≤ t) (htl : t ≤ l) : rowCross Y r s k t = 0 :=
  le_antisymm (rowCross_nonpos_of_le h₂ hrs hρ hr hs htl)
    (rowCross_nonneg_of_le h₂ hrs hkt)

theorem columnDifference_nonneg (h₂ : TP2 Y) {i h : ι} {k l : κ} {ρ : ℝ}
    (hkl : k < l) (hik : 0 < Y i k)
    (hi : columnDifference Y k l ρ i = 0) (hih : i ≤ h) :
    0 ≤ columnDifference Y k l ρ h := by
  rcases eq_or_lt_of_le hih with rfl | hih
  · exact le_of_eq hi.symm
  · have hi' : Y i l = ρ * Y i k := sub_eq_zero.mp hi
    have hminor := h₂ i h k l hih hkl
    rw [hi'] at hminor
    by_contra h
    have hprod := mul_neg_of_pos_of_neg hik (lt_of_not_ge h)
    dsimp [columnDifference] at hprod
    nlinarith

theorem columnDifference_nonpos (h₂ : TP2 Y) {h j : ι} {k l : κ} {ρ : ℝ}
    (hkl : k < l) (hjk : 0 < Y j k)
    (hj : columnDifference Y k l ρ j = 0) (hhj : h ≤ j) :
    columnDifference Y k l ρ h ≤ 0 := by
  rcases eq_or_lt_of_le hhj with rfl | hhj
  · exact le_of_eq hj
  · have hj' : Y j l = ρ * Y j k := sub_eq_zero.mp hj
    have hminor := h₂ h j k l hhj hkl
    rw [hj'] at hminor
    by_contra h
    have hprod := mul_pos hjk (lt_of_not_ge h)
    dsimp [columnDifference] at hprod
    nlinarith

theorem signed_rowCross_mul_difference_nonpos {η ρ : ℝ}
    (h₃ : SignedThreeMinors η Y) {r s h : ι} {k l t : κ}
    (hrs : r < s) (hkl : k < l)
    (hh : h < r ∨ s < h) (ht : t < k ∨ l < t)
    (hr : columnDifference Y k l ρ r = 0)
    (hs : columnDifference Y k l ρ s = 0) :
    (η * rowCross Y r s k t) * columnDifference Y k l ρ h ≤ 0 := by
  have hsign := h₃.external hrs hkl hh ht
  rw [detThree_anchor_identity hr hs] at hsign
  nlinarith

end Ordered

private theorem eq_zero_of_opposite_products {x a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (hxa : x * a ≤ 0) (hxb : x * b ≤ 0) :
    x = 0 := by
  apply le_antisymm
  · by_contra h
    have := mul_pos (lt_of_not_ge h) hb
    linarith
  · by_contra h
    have := mul_pos_of_neg_of_neg (lt_of_not_ge h) ha
    linarith

theorem exists_nonzero_columnDifference {n : ℕ} {Y : Square n}
    (hdet : Matrix.det Y ≠ 0) {k l : Fin n} (hkl : k < l) (ρ : ℝ) :
    ∃ h, columnDifference Y k l ρ h ≠ 0 := by
  classical
  by_contra hex
  have hz : ∀ h, columnDifference Y k l ρ h = 0 :=
    fun h => Classical.byContradiction (fun hn => hex ⟨h, hn⟩)
  have heq : (1 : ℝ) • Y.col l = ρ • Y.col k := by
    ext h
    simpa only [Pi.smul_apply, one_smul, smul_eq_mul, Matrix.col_apply, one_mul] using
      (sub_eq_zero.mp (hz h))
  have heqidx := (Matrix.linearIndependent_cols_of_det_ne_zero hdet).eq_of_smul_apply_eq_smul_apply
    1 ρ l k one_ne_zero heq
  exact hkl.ne heqidx.symm

/-- Two strict column differences of opposite signs would make the
anchor rows proportional, contradicting nonsingularity. -/
theorem not_opposite_columnDifferences {n : ℕ} {Y : Square n} {η ρ : ℝ}
    (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0)
    (h₃ : SignedThreeMinors η Y) (hη : η ≠ 0)
    {i j k l : Fin n} (hij : i < j) (hkl : k < l)
    (hρ : 0 < ρ) (hik : 0 < Y i k) (hjk : 0 < Y j k)
    (hi : columnDifference Y k l ρ i = 0)
    (hj : columnDifference Y k l ρ j = 0)
    {hm hp : Fin n}
    (hmneg : columnDifference Y k l ρ hm < 0)
    (hppos : 0 < columnDifference Y k l ρ hp) : False := by
  have hmi : hm < i := by
    by_contra h
    have := columnDifference_nonneg h₂ hkl hik hi (le_of_not_gt h)
    linarith
  have hjp : j < hp := by
    by_contra h
    have := columnDifference_nonpos h₂ hkl hjk hj (le_of_not_gt h)
    linarith
  have hcross (t : Fin n) : rowCross Y i j k t = 0 := by
    have hout (ht : t < k ∨ l < t) : rowCross Y i j k t = 0 := by
      have hmprod := signed_rowCross_mul_difference_nonpos h₃ hij hkl
        (Or.inl hmi) ht hi hj
      have hpprod := signed_rowCross_mul_difference_nonpos h₃ hij hkl
        (Or.inr hjp) ht hi hj
      have hmul := eq_zero_of_opposite_products hmneg hppos hmprod hpprod
      exact (mul_eq_zero.mp hmul).resolve_left hη
    by_cases htk : t < k
    · exact hout (Or.inl htk)
    by_cases hlt : l < t
    · exact hout (Or.inr hlt)
    exact rowCross_zero_between h₂ hij hρ hi hj
      (le_of_not_gt htk) (le_of_not_gt hlt)
  have heq : Y i k • Y j = Y j k • Y i := by
    ext t
    exact sub_eq_zero.mp (hcross t)
  have heqidx := (Matrix.linearIndependent_rows_of_det_ne_zero hdet).eq_of_smul_apply_eq_smul_apply
    (Y i k) (Y j k) j i (ne_of_gt hik) heq
  exact hij.ne heqidx.symm

def TopCornerColumns {κ : Type*} [LE κ] (η : ℝ) (k l : κ) (t : κ) : Prop :=
  (η = 1 ∧ k ≤ t) ∨ (η = -1 ∧ t ≤ l)

def BottomCornerColumns {κ : Type*} [LE κ] (η : ℝ) (k l : κ) (t : κ) : Prop :=
  (η = 1 ∧ t ≤ l) ∨ (η = -1 ∧ k ≤ t)

theorem top_corner_factor_of_later_difference {n : ℕ} {Y : Square n} {η ρ : ℝ}
    (h₂ : TP2 Y) (h₃ : SignedThreeMinors η Y)
    {j h k l : Fin n} (hkl : k < l) (hjh : j < h)
    (hρ : 0 < ρ) (hjk : 0 < Y j k)
    (hz : ∀ r, r ≤ j → columnDifference Y k l ρ r = 0)
    (hq : 0 < columnDifference Y k l ρ h) :
    RankOneOn Y (fun r => r ≤ j) (TopCornerColumns η k l) := by
  refine ⟨fun r => Y r k / Y j k, fun t => Y j t, ?_⟩
  intro r hr t ht
  have hcross : rowCross Y r j k t = 0 := by
    rcases eq_or_lt_of_le hr with rfl | hrj
    · simp [rowCross]
    have hrz := hz r hrj.le
    have hjz := hz j le_rfl
    rcases ht with ⟨hη, hkt⟩ | ⟨hη, htl⟩
    · by_cases htl : t ≤ l
      · exact rowCross_zero_between h₂ hrj hρ hrz hjz hkt htl
      have hprod := signed_rowCross_mul_difference_nonpos h₃ hrj hkl
        (Or.inr hjh) (Or.inr (lt_of_not_ge htl)) hrz hjz
      rw [hη, one_mul] at hprod
      have hle : rowCross Y r j k t ≤ 0 := by
        by_contra hn
        have := mul_pos (lt_of_not_ge hn) hq
        linarith
      exact le_antisymm hle (rowCross_nonneg_of_le h₂ hrj hkt)
    · by_cases hkt : k ≤ t
      · exact rowCross_zero_between h₂ hrj hρ hrz hjz hkt htl
      have hprod := signed_rowCross_mul_difference_nonpos h₃ hrj hkl
        (Or.inr hjh) (Or.inl (lt_of_not_ge hkt)) hrz hjz
      rw [hη] at hprod
      have hge : 0 ≤ rowCross Y r j k t := by
        by_contra hn
        have := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hq
        nlinarith
      exact le_antisymm (rowCross_nonpos_of_le h₂ hrj hρ hrz hjz htl) hge
  dsimp [rowCross] at hcross
  field_simp [ne_of_gt hjk]
  nlinarith

theorem bottom_corner_factor_of_earlier_difference {n : ℕ} {Y : Square n} {η ρ : ℝ}
    (h₂ : TP2 Y) (h₃ : SignedThreeMinors η Y)
    {i h k l : Fin n} (hkl : k < l) (hhi : h < i)
    (hρ : 0 < ρ) (hik : 0 < Y i k)
    (hz : ∀ r, i ≤ r → columnDifference Y k l ρ r = 0)
    (hq : columnDifference Y k l ρ h < 0) :
    RankOneOn Y (fun r => i ≤ r) (BottomCornerColumns η k l) := by
  refine ⟨fun r => Y r k / Y i k, fun t => Y i t, ?_⟩
  intro r hr t ht
  have hcross : rowCross Y i r k t = 0 := by
    rcases eq_or_lt_of_le hr with rfl | hir
    · simp [rowCross]
    have hiz := hz i le_rfl
    have hrz := hz r hir.le
    rcases ht with ⟨hη, htl⟩ | ⟨hη, hkt⟩
    · by_cases hkt : k ≤ t
      · exact rowCross_zero_between h₂ hir hρ hiz hrz hkt htl
      have hprod := signed_rowCross_mul_difference_nonpos h₃ hir hkl
        (Or.inl hhi) (Or.inl (lt_of_not_ge hkt)) hiz hrz
      rw [hη, one_mul] at hprod
      have hge : 0 ≤ rowCross Y i r k t := by
        by_contra hn
        have := mul_pos_of_neg_of_neg (lt_of_not_ge hn) hq
        linarith
      exact le_antisymm (rowCross_nonpos_of_le h₂ hir hρ hiz hrz htl) hge
    · by_cases htl : t ≤ l
      · exact rowCross_zero_between h₂ hir hρ hiz hrz hkt htl
      have hprod := signed_rowCross_mul_difference_nonpos h₃ hir hkl
        (Or.inl hhi) (Or.inr (lt_of_not_ge htl)) hiz hrz
      rw [hη] at hprod
      have hle : rowCross Y i r k t ≤ 0 := by
        by_contra hn
        have := mul_neg_of_pos_of_neg (lt_of_not_ge hn) hq
        nlinarith
      exact le_antisymm hle (rowCross_nonneg_of_le h₂ hir hkt)
  dsimp [rowCross] at hcross
  field_simp [ne_of_gt hik]
  nlinarith

/-- Section 3.1, existence of the appropriate attached rank-one corner,
stated as an explicit outer-product factorization on its index rectangle. -/
theorem rankOneCorner_of_positive_zero_two {n : ℕ} {Y : Square n} {η : ℝ}
    (h₂ : TP2 Y) (hdet : Matrix.det Y ≠ 0) (h₃ : SignedThreeMinors η Y)
    (hη : η = 1 ∨ η = -1) {i j k l : Fin n}
    (hij : i < j) (hkl : k < l)
    (hik : 0 < Y i k) (hil : 0 < Y i l) (hjk : 0 < Y j k)
    (hanchor : Y i k * Y j l - Y i l * Y j k = 0) :
    RankOneOn Y (fun r => r ≤ j) (TopCornerColumns η k l) ∨
      RankOneOn Y (fun r => i ≤ r) (BottomCornerColumns η k l) := by
  let ρ : ℝ := Y i l / Y i k
  have hρ : 0 < ρ := div_pos hil hik
  have hi : columnDifference Y k l ρ i = 0 := by
    dsimp [columnDifference, ρ]
    field_simp [ne_of_gt hik]
    ring
  have hj : columnDifference Y k l ρ j = 0 := by
    dsimp [columnDifference, ρ]
    field_simp [ne_of_gt hik]
    nlinarith
  have hηne : η ≠ 0 := by rcases hη with rfl | rfl <;> norm_num
  obtain ⟨h, hh⟩ := exists_nonzero_columnDifference hdet hkl ρ
  rcases lt_or_gt_of_ne hh with hhneg | hhpos
  · have hhi : h < i := by
      by_contra hn
      have := columnDifference_nonneg h₂ hkl hik hi (le_of_not_gt hn)
      linarith
    have hz : ∀ r, i ≤ r → columnDifference Y k l ρ r = 0 := by
      intro r hir
      have hnonneg := columnDifference_nonneg h₂ hkl hik hi hir
      apply le_antisymm _ hnonneg
      by_contra hn
      exact not_opposite_columnDifferences h₂ hdet h₃ hηne hij hkl hρ hik hjk
        hi hj hhneg (lt_of_not_ge hn)
    exact Or.inr (bottom_corner_factor_of_earlier_difference h₂ h₃ hkl hhi hρ hik hz hhneg)
  · have hjh : j < h := by
      by_contra hn
      have := columnDifference_nonpos h₂ hkl hjk hj (le_of_not_gt hn)
      linarith
    have hz : ∀ r, r ≤ j → columnDifference Y k l ρ r = 0 := by
      intro r hrj
      have hnonpos := columnDifference_nonpos h₂ hkl hjk hj hrj
      apply le_antisymm hnonpos
      by_contra hn
      exact not_opposite_columnDifferences h₂ hdet h₃ hηne hij hkl hρ hik hjk
        hi hj (lt_of_not_ge hn) hhpos
    exact Or.inl (top_corner_factor_of_later_difference h₂ h₃ hkl hjh hρ hjk hz hhpos)

theorem RankOneOn.finset_card_bound {n : ℕ} {Y : Square n}
    {R C : Fin n → Prop} (hf : RankOneOn Y R C)
    (hdet : Matrix.det Y ≠ 0) (rows cols : Finset (Fin n))
    (hr : ∀ r ∈ rows, R r) (hc : ∀ c ∈ cols, C c) :
    rows.card + cols.card ≤ n + 1 := by
  classical
  obtain ⟨u, v, huv⟩ := hf
  have h := cards_le_card_add_one_of_submatrix_outer_product Y hdet
    (fun r : rows => r.val) (fun c : cols => c.val)
    Subtype.val_injective Subtype.val_injective
    ⟨fun r => u r.val, fun c => v c.val,
      fun r c => huv r.val (hr r.val r.property) c.val (hc c.val c.property)⟩
  simpa only [Fintype.card_coe, Fintype.card_fin] using h

theorem RankOneOn.nw_index_bound {n : ℕ} {Y : Square n} {j l : Fin n}
    (hf : RankOneOn Y (fun r => r ≤ j) (fun c => c ≤ l))
    (hdet : Matrix.det Y ≠ 0) : j.val + l.val + 1 ≤ n := by
  have h := hf.finset_card_bound hdet (Finset.Iic j) (Finset.Iic l)
    (fun _ h => Finset.mem_Iic.mp h) (fun _ h => Finset.mem_Iic.mp h)
  rw [Fin.card_Iic, Fin.card_Iic] at h
  omega

theorem RankOneOn.ne_index_bound {n : ℕ} {Y : Square n} {j k : Fin n}
    (hf : RankOneOn Y (fun r => r ≤ j) (fun c => k ≤ c))
    (hdet : Matrix.det Y ≠ 0) : j ≤ k := by
  have h := hf.finset_card_bound hdet (Finset.Iic j) (Finset.Ici k)
    (fun _ h => Finset.mem_Iic.mp h) (fun _ h => Finset.mem_Ici.mp h)
  rw [Fin.card_Iic, Fin.card_Ici] at h
  have hk := k.isLt
  change j.val ≤ k.val
  omega

theorem RankOneOn.sw_index_bound {n : ℕ} {Y : Square n} {i l : Fin n}
    (hf : RankOneOn Y (fun r => i ≤ r) (fun c => c ≤ l))
    (hdet : Matrix.det Y ≠ 0) : l ≤ i := by
  have h := hf.finset_card_bound hdet (Finset.Ici i) (Finset.Iic l)
    (fun _ h => Finset.mem_Ici.mp h) (fun _ h => Finset.mem_Iic.mp h)
  rw [Fin.card_Ici, Fin.card_Iic] at h
  have hi := i.isLt
  change l.val ≤ i.val
  omega

theorem RankOneOn.se_index_bound {n : ℕ} {Y : Square n} {i k : Fin n}
    (hf : RankOneOn Y (fun r => i ≤ r) (fun c => k ≤ c))
    (hdet : Matrix.det Y ≠ 0) : n ≤ i.val + k.val + 1 := by
  have h := hf.finset_card_bound hdet (Finset.Ici i) (Finset.Ici k)
    (fun _ h => Finset.mem_Ici.mp h) (fun _ h => Finset.mem_Ici.mp h)
  rw [Fin.card_Ici, Fin.card_Ici] at h
  have hi := i.isLt
  have hk := k.isLt
  omega

/-- Opposite permitted orientations are incompatible even for two different
invertible matrices. This is the endpoint-independent uniqueness required in
Section 7.1, rather than merely uniqueness inside a single matrix. -/
theorem no_opposite_corner_orientations {n : ℕ} {A B : Square n} {η : ℝ}
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0)
    (hη : η = 1 ∨ η = -1) {i j k l : Fin n}
    (hij : i < j) (hkl : k < l)
    (htop : RankOneOn A (fun r => r ≤ j) (TopCornerColumns η k l))
    (hbottom : RankOneOn B (fun r => i ≤ r) (BottomCornerColumns η k l)) : False := by
  rcases hη with rfl | rfl
  · have ht : RankOneOn A (fun r => r ≤ j) (fun c => k ≤ c) := by
      simpa [RankOneOn, TopCornerColumns, show (1 : ℝ) ≠ -1 by norm_num] using htop
    have hb : RankOneOn B (fun r => i ≤ r) (fun c => c ≤ l) := by
      simpa [RankOneOn, BottomCornerColumns, show (1 : ℝ) ≠ -1 by norm_num] using hbottom
    have hjk := ht.ne_index_bound hA
    have hli := hb.sw_index_bound hB
    exact (not_lt_of_ge hli) (lt_of_lt_of_le (lt_of_lt_of_le hij hjk) hkl.le)
  · have ht : RankOneOn A (fun r => r ≤ j) (fun c => c ≤ l) := by
      simpa [RankOneOn, TopCornerColumns, show (-1 : ℝ) ≠ 1 by norm_num] using htop
    have hb : RankOneOn B (fun r => i ≤ r) (fun c => k ≤ c) := by
      simpa [RankOneOn, BottomCornerColumns, show (-1 : ℝ) ≠ 1 by norm_num] using hbottom
    have htopbound := ht.nw_index_bound hA
    have hbotbound := hb.se_index_bound hB
    change i.val < j.val at hij
    change k.val < l.val at hkl
    omega

/-- The two endpoints have the same attached rank-one corner whenever
the two-corner alternatives hold at the same indices. -/
theorem common_corner_orientation {n : ℕ} {A B : Square n} {η : ℝ}
    (hA : Matrix.det A ≠ 0) (hB : Matrix.det B ≠ 0)
    (hη : η = 1 ∨ η = -1) {i j k l : Fin n}
    (hij : i < j) (hkl : k < l)
    (hAc : RankOneOn A (fun r => r ≤ j) (TopCornerColumns η k l) ∨
      RankOneOn A (fun r => i ≤ r) (BottomCornerColumns η k l))
    (hBc : RankOneOn B (fun r => r ≤ j) (TopCornerColumns η k l) ∨
      RankOneOn B (fun r => i ≤ r) (BottomCornerColumns η k l)) :
    (RankOneOn A (fun r => r ≤ j) (TopCornerColumns η k l) ∧
      RankOneOn B (fun r => r ≤ j) (TopCornerColumns η k l)) ∨
    (RankOneOn A (fun r => i ≤ r) (BottomCornerColumns η k l) ∧
      RankOneOn B (fun r => i ≤ r) (BottomCornerColumns η k l)) := by
  rcases hAc with hat | hab <;> rcases hBc with hbt | hbb
  · exact Or.inl ⟨hat, hbt⟩
  · exact (no_opposite_corner_orientations hA hB hη hij hkl hat hbb).elim
  · exact (no_opposite_corner_orientations hB hA hη hij hkl hbt hab).elim
  · exact Or.inr ⟨hab, hbb⟩

end IV01
