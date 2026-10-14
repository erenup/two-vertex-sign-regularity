import IV01.RankMinors
import IV01.SchurClosure

namespace IV01

open Matrix Module

lemma linearIndepOn_card_eq_finrank_image_span
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (v : ι → V) (s : Finset ι)
    (h : LinearIndepOn ℝ v (s : Set ι)) :
    s.card = finrank ℝ (Submodule.span ℝ (v '' (s : Set ι))) := by
  have hc := linearIndependent_iff_card_eq_finrank_span.mp h
  change Fintype.card s = finrank ℝ
    (Submodule.span ℝ (Set.range (fun i : s => v i))) at hc
  rw [show Set.range (fun i : s => v i) = v '' (s : Set ι) by
    ext x
    simp] at hc
  simpa only [Fintype.card_coe] using hc

/-- Complete the span of a prescribed subfamily to exactly `p` independent
members of the original finite family. No arbitrary new vectors are used. -/
theorem exists_increasing_independent_cover
    {ι V : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (v : ι → V) (s : Set ι) (p : ℕ)
    (hs : finrank ℝ (Submodule.span ℝ (v '' s)) ≤ p)
    (hp : p ≤ finrank ℝ (Submodule.span ℝ (Set.range v))) :
    ∃ L : Fin p → ι, StrictMono L ∧ LinearIndependent ℝ (v ∘ L) ∧
      ∀ j ∈ s, v j ∈ Submodule.span ℝ (Set.range (v ∘ L)) := by
  classical
  obtain ⟨B₀, hB₀s, _, hspan₀, hli₀⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ v) (Set.empty_subset s)
  obtain ⟨B, _, hB₀B, hspanB, hliB⟩ :=
    exists_linearIndepOn_extension hli₀ (Set.subset_univ B₀)
  let b₀ : Finset ι := B₀.toFinite.toFinset
  let b : Finset ι := B.toFinite.toFinset
  have hb₀ : (b₀ : Set ι) = B₀ := by simp [b₀]
  have hb : (b : Set ι) = B := by simp [b]
  have hc₀ : b₀.card = finrank ℝ (Submodule.span ℝ (v '' B₀)) := by
    rw [← hb₀]
    exact linearIndepOn_card_eq_finrank_image_span v b₀ (by rwa [hb₀])
  have hcB : b.card = finrank ℝ (Submodule.span ℝ (v '' B)) := by
    rw [← hb]
    exact linearIndepOn_card_eq_finrank_image_span v b (by rwa [hb])
  have hsmall : b₀.card ≤ p := by
    rw [hc₀]
    exact (Submodule.finrank_mono (Submodule.span_mono (Set.image_mono hB₀s))).trans hs
  have hlarge : p ≤ b.card := by
    rw [hcB]
    apply hp.trans
    apply Submodule.finrank_mono
    apply Submodule.span_le.mpr
    simpa only [Set.image_univ] using hspanB
  have hsubset : b₀ ⊆ b := by
    change (b₀ : Set ι) ⊆ b
    rwa [hb₀, hb]
  obtain ⟨u, hb₀u, hub, hucard⟩ := Finset.exists_subsuperset_card_eq hsubset hsmall hlarge
  let L : Fin p ↪o ι := u.orderEmbOfFin hucard
  have hrange : Set.range L = (u : Set ι) := Finset.range_orderEmbOfFin u hucard
  have hliU : LinearIndepOn ℝ v (u : Set ι) := hliB.mono (by
    rw [← hb]
    exact hub)
  refine ⟨L, L.strictMono, (linearIndepOn_range_iff L.injective v).mp ?_, ?_⟩
  · rwa [hrange]
  · intro j hj
    rw [Set.range_comp, hrange]
    apply Submodule.span_mono (Set.image_mono (show B₀ ⊆ (u : Set ι) by
      rw [← hb₀]
      exact hb₀u))
    exact hspan₀ ⟨j, hj, rfl⟩

end IV01
