import IV01.FeketeIdentity
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import IV01.SolidMinors

namespace IV01

/-- The increasing map omitting the first and last indices. -/
def middleIndices {q : ℕ} (i : Fin q) : Fin (q + 2) := i.succ.castSucc

theorem strictMono_middleIndices {q : ℕ} : StrictMono (@middleIndices q) := by
  intro a b h
  change a.val + 1 < b.val + 1
  have hab : a.val < b.val := h
  omega

def indexSpan {n q : ℕ} (cols : Fin (q + 2) → Fin n) : ℕ :=
  (cols (Fin.last (q + 1))).val - (cols 0).val

abbrev InteriorColumns {n q : ℕ} (cols : Fin (q + 2) → Fin n) :=
  {c : Fin n // cols 0 < c ∧ c < cols (Fin.last (q + 1))}

theorem middleIndices_pos {q : ℕ} (i : Fin q) : (0 : Fin (q + 2)) < middleIndices i := by
  change 0 < i.val + 1
  omega

theorem middleIndices_lt_last {q : ℕ} (i : Fin q) : middleIndices i < Fin.last (q + 1) := by
  change i.val + 1 < q + 1
  have h := i.isLt
  omega

theorem exists_middleIndices_of_between {q : ℕ} (i : Fin (q + 2))
    (h0 : 0 < i) (hl : i < Fin.last (q + 1)) : ∃ j : Fin q, middleIndices j = i := by
  have h0' : 0 < i.val := h0
  have hl' : i.val < q + 1 := hl
  refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
  apply Fin.ext
  change (i.val - 1) + 1 = i.val
  omega

theorem mem_range_middle_iff {n q : ℕ} (cols : Fin (q + 2) → Fin n)
    (hc : StrictMono cols) (c : Fin n) :
    c ∈ Set.range (cols ∘ middleIndices) ↔
      c ∈ Set.range cols ∧ cols 0 < c ∧ c < cols (Fin.last (q + 1)) := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨middleIndices i, rfl⟩, hc (middleIndices_pos i), hc (middleIndices_lt_last i)⟩
  · rintro ⟨⟨i, rfl⟩, h0, hl⟩
    obtain ⟨j, hj⟩ := exists_middleIndices_of_between i
      (hc.lt_iff_lt.mp h0) (hc.lt_iff_lt.mp hl)
    exact ⟨j, by change cols (middleIndices j) = cols i; rw [hj]⟩

/-- The selected core columns lie in the full open interior interval. -/
def coreToInterior {n q : ℕ} (cols : Fin (q + 2) → Fin n) (hc : StrictMono cols) :
    Fin q → InteriorColumns cols := fun i =>
  ⟨cols (middleIndices i), hc (middleIndices_pos i), hc (middleIndices_lt_last i)⟩

theorem strictMono_coreToInterior {n q : ℕ} (cols : Fin (q + 2) → Fin n)
    (hc : StrictMono cols) : StrictMono (coreToInterior cols hc) :=
  hc.comp strictMono_middleIndices

theorem indexSpan_drop_first_lt {n q : ℕ}
    (all : Fin (q + 3) → Fin n) (ha : StrictMono all)
    (cols : Fin (q + 2) → Fin n)
    (h0 : all 0 = cols 0) (hl : all (Fin.last (q + 2)) = cols (Fin.last (q + 1))) :
    indexSpan (all ∘ Fin.succ) < indexSpan cols := by
  have h01 : (all 0).val < (all (Fin.succ (0 : Fin (q + 2)))).val :=
    ha (Fin.succ_pos 0)
  have h1l : (all (Fin.succ (0 : Fin (q + 2)))).val ≤
      (all (Fin.last (q + 2))).val := ha.monotone (Fin.le_last _)
  unfold indexSpan
  change (all (Fin.last (q + 2))).val - (all (Fin.succ (0 : Fin (q + 2)))).val < _
  rw [h0] at h01
  rw [hl] at h1l
  rw [hl]
  omega

theorem indexSpan_drop_last_lt {n q : ℕ}
    (all : Fin (q + 3) → Fin n) (ha : StrictMono all)
    (cols : Fin (q + 2) → Fin n)
    (h0 : all 0 = cols 0) (hl : all (Fin.last (q + 2)) = cols (Fin.last (q + 1))) :
    indexSpan (all ∘ Fin.castSucc) < indexSpan cols := by
  have h01 : (all 0).val ≤ (all (Fin.castSucc (Fin.last (q + 1)))).val :=
    ha.monotone (Fin.zero_le _)
  have h1l : (all (Fin.castSucc (Fin.last (q + 1)))).val <
      (all (Fin.last (q + 2))).val := ha (by change q + 1 < q + 2; omega)
  unfold indexSpan
  change (all (Fin.castSucc (Fin.last (q + 1)))).val - (all 0).val < _
  rw [h0] at h01
  rw [hl] at h1l
  rw [h0]
  omega

/-- Insert a missing interior column into an increasing column family. The
old family is exactly the new sorted family with that interior position deleted. -/
theorem exists_sorted_interior_insertion {n q : ℕ}
    (cols : Fin (q + 2) → Fin n) (hc : StrictMono cols) (c : Fin n)
    (hfirst : cols 0 < c) (hlast : c < cols (Fin.last (q + 1)))
    (hmissing : c ∉ Set.range cols) :
    ∃ (all : Fin (q + 3) → Fin n) (b : Fin (q + 1)),
      StrictMono all ∧ all (feketeInterior b) = c ∧
      all ∘ (feketeInterior b).succAbove = cols ∧
      all 0 = cols 0 ∧ all (Fin.last (q + 2)) = cols (Fin.last (q + 1)) := by
  classical
  let s : Finset (Fin n) := insert c (Finset.univ.image cols)
  have hnot : c ∉ Finset.univ.image cols := by simpa only [Finset.mem_image, Finset.mem_univ,
    true_and, Set.mem_range] using hmissing
  have hs : s.card = q + 3 := by
    rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ hc.injective,
      Finset.card_univ, Fintype.card_fin]
  let all : Fin (q + 3) ↪o Fin n := s.orderEmbOfFin hs
  have hrange : Set.range all = insert c (Set.range cols) := by
    rw [Finset.range_orderEmbOfFin]
    simp only [s, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  obtain ⟨t, ht⟩ : c ∈ Set.range all := by rw [hrange]; exact Set.mem_insert _ _
  have h0 : all 0 = cols 0 := by
    apply le_antisymm
    · obtain ⟨u, hu⟩ : cols 0 ∈ Set.range all := by
        rw [hrange]
        exact Set.mem_insert_of_mem _ ⟨0, rfl⟩
      rw [← hu]
      exact all.monotone (Fin.zero_le u)
    · have hx : all 0 ∈ insert c (Set.range cols) := by rw [← hrange]; exact ⟨0, rfl⟩
      rcases hx with hx | ⟨u, hu⟩
      · rw [hx]
        exact hfirst.le
      · rw [← hu]
        exact hc.monotone (Fin.zero_le u)
  have hlast' : all (Fin.last (q + 2)) = cols (Fin.last (q + 1)) := by
    apply le_antisymm
    · have hx : all (Fin.last (q + 2)) ∈ insert c (Set.range cols) := by
        rw [← hrange]
        exact ⟨Fin.last (q + 2), rfl⟩
      rcases hx with hx | ⟨u, hu⟩
      · rw [hx]
        exact hlast.le
      · rw [← hu]
        exact hc.monotone (Fin.le_last u)
    · obtain ⟨u, hu⟩ : cols (Fin.last (q + 1)) ∈ Set.range all := by
        rw [hrange]
        exact Set.mem_insert_of_mem _ ⟨Fin.last (q + 1), rfl⟩
      rw [← hu]
      exact all.monotone (Fin.le_last u)
  have ht0 : 0 < t := by
    apply all.strictMono.lt_iff_lt.mp
    simpa only [h0, ht] using hfirst
  have htlast : t < Fin.last (q + 2) := by
    apply all.strictMono.lt_iff_lt.mp
    simpa only [hlast', ht] using hlast
  let b : Fin (q + 1) := ⟨t.val - 1, by
    have htl : t.val < q + 2 := htlast
    have htz : 0 < t.val := ht0
    omega⟩
  have hb : feketeInterior b = t := by
    apply Fin.ext
    change (t.val - 1) + 1 = t.val
    have htz : 0 < t.val := ht0
    omega
  refine ⟨all, b, all.strictMono, hb ▸ ht, ?_, h0, hlast'⟩
  apply (all.strictMono.comp (Fin.strictMono_succAbove _)).eq_of_range_eq hc
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hx : all ((feketeInterior b).succAbove u) ∈ insert c (Set.range cols) := by
      rw [← hrange]
      exact ⟨_, rfl⟩
    rcases hx with hx | hx
    · have ht' : (feketeInterior b).succAbove u = t := all.injective (hx.trans ht.symm)
      exact False.elim (Fin.succAbove_ne (feketeInterior b) u (ht'.trans hb.symm))
    · exact hx
  · intro hx
    obtain ⟨u, hu⟩ : x ∈ Set.range all := by rw [hrange]; exact Set.mem_insert_of_mem _ hx
    have hut : u ≠ t := by
      intro hut
      apply hmissing
      rw [← hu, hut, ht] at hx
      exact hx
    obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq (by simpa only [hb] using hut)
    exact ⟨v, by change all ((feketeInterior b).succAbove v) = x; rw [hb, hv]; exact hu⟩

theorem card_interior_ge_of_gap {n q : ℕ}
    (cols : Fin (q + 2) → Fin n) (hc : StrictMono cols)
    (hgap : ∃ c : InteriorColumns cols, c.val ∉ Set.range cols) :
    q + 1 ≤ Fintype.card (InteriorColumns cols) := by
  classical
  obtain ⟨c, hmissing⟩ := hgap
  obtain ⟨all, b, hall, hb, hd, h0, hl⟩ :=
    exists_sorted_interior_insertion cols hc c.val c.property.1 c.property.2 hmissing
  let e : Fin (q + 1) → InteriorColumns cols := fun i =>
    ⟨all (feketeInterior i), by
      rw [← h0, ← hl]
      exact ⟨hall (middleIndices_pos i), hall (middleIndices_lt_last i)⟩⟩
  have he : Function.Injective e := by
    intro i j hij
    exact strictMono_feketeInterior.injective (hall.injective (congrArg Subtype.val hij))
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he

/-- Every increasing family is consecutive or omits a column strictly between
its endpoints. -/
theorem consecutive_or_gap {n q : ℕ}
    (cols : Fin (q + 2) → Fin n) (hc : StrictMono cols) :
    (∃ (a : ℕ) (ha : a + (q + 2) ≤ n), cols = consecutiveIndices n (q + 2) a ha) ∨
      (∃ c : InteriorColumns cols, c.val ∉ Set.range cols) := by
  classical
  by_cases hg : ∃ c : InteriorColumns cols, c.val ∉ Set.range cols
  · exact Or.inr hg
  left
  have hcover : ∀ c : Fin n, cols 0 ≤ c → c ≤ cols (Fin.last (q + 1)) → c ∈ Set.range cols := by
    intro c h0 hl
    by_cases he0 : c = cols 0
    · exact ⟨0, he0.symm⟩
    by_cases hel : c = cols (Fin.last (q + 1))
    · exact ⟨Fin.last (q + 1), hel.symm⟩
    by_contra hnot
    exact hg ⟨⟨c, lt_of_le_of_ne h0 (Ne.symm he0), lt_of_le_of_ne hl hel⟩, hnot⟩
  have himage : Finset.univ.image cols = Finset.Icc (cols 0) (cols (Fin.last (q + 1))) := by
    ext c
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨hc.monotone (Fin.zero_le i), hc.monotone (Fin.le_last i)⟩
    · rintro ⟨h0, hl⟩
      exact hcover c h0 hl
  have hcard : q + 2 = (cols (Fin.last (q + 1))).val + 1 - (cols 0).val := by
    have h := congrArg Finset.card himage
    simpa only [Finset.card_image_of_injective _ hc.injective,
      Finset.card_univ, Fintype.card_fin, Fin.card_Icc] using h
  have hle : (cols 0).val ≤ (cols (Fin.last (q + 1))).val :=
    hc.monotone (Fin.zero_le _)
  have ha : (cols 0).val + (q + 2) ≤ n := by
    have hlt := (cols (Fin.last (q + 1))).isLt
    omega
  refine ⟨(cols 0).val, ha, hc.eq_of_range_eq (consecutiveIndices_strictMono ha) ?_⟩
  ext c
  constructor
  · rintro ⟨i, rfl⟩
    have hi0 : (cols 0).val ≤ (cols i).val := hc.monotone (Fin.zero_le i)
    have hil : (cols i).val ≤ (cols (Fin.last (q + 1))).val := hc.monotone (Fin.le_last i)
    refine ⟨⟨(cols i).val - (cols 0).val, by omega⟩, ?_⟩
    apply Fin.ext
    change (cols 0).val + ((cols i).val - (cols 0).val) = (cols i).val
    omega
  · rintro ⟨i, rfl⟩
    apply hcover
    · change (cols 0).val ≤ (cols 0).val + i.val
      omega
    · change (cols 0).val + i.val ≤ (cols (Fin.last (q + 1))).val
      have hi := i.isLt
      omega

end IV01
