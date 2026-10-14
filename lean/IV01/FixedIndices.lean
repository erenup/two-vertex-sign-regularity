import IV01.FixedRectangle
import IV01.MinimalBad
import IV01.PivotIndices
import IV01.SchurSetup

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem exists_perm_of_range_subset {α : Type*} {k : ℕ}
    (f g : Fin k → α) (hf : Function.Injective f) (_hg : Function.Injective g)
    (hmem : ∀ i, f i ∈ Set.range g) :
    ∃ σ : Equiv.Perm (Fin k), f = g ∘ σ := by
  classical
  choose s hs using hmem
  have hsinj : Function.Injective s := by
    intro i j hij
    apply hf
    rw [← hs i, ← hs j, hij]
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj)
  exact ⟨σ, funext (fun i => (hs i).symm)⟩

theorem mem_range_drop_last {α : Type*} {k : ℕ}
    (f : Fin (k + 1) → α) {x : α} (hx : x ∈ Set.range f)
    (hne : x ≠ f (Fin.last k)) : x ∈ Set.range (f ∘ Fin.castSucc) := by
  obtain ⟨i, rfl⟩ := hx
  revert hne
  refine Fin.lastCases ?_ ?_ i
  · intro h
    exact (h rfl).elim
  · intro j _
    exact ⟨j, rfl⟩

theorem mem_range_drop_first {α : Type*} {k : ℕ}
    (f : Fin (k + 1) → α) {x : α} (hx : x ∈ Set.range f)
    (hne : x ≠ f 0) : x ∈ Set.range (f ∘ Fin.succ) := by
  obtain ⟨i, rfl⟩ := hx
  revert hne
  refine Fin.cases ?_ ?_ i
  · intro h
    exact (h rfl).elim
  · intro j _
    exact ⟨j, rfl⟩

theorem exists_extra_interior_column {n q : ℕ}
    (J : Fin (q + 2) → Fin n) (hJ : StrictMono J)
    (hcard : q + 1 ≤ Fintype.card (InteriorColumns J)) :
    ∃ b : InteriorColumns J, b.val ∉ Set.range (J ∘ middleIndices) := by
  classical
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (coreToInterior J hJ) := by
    intro b
    obtain ⟨i, hi⟩ := h b
    exact ⟨i, Subtype.ext hi⟩
  have hle := Fintype.card_le_of_surjective (coreToInterior J hJ) hsurj
  simp only [Fintype.card_fin] at hle
  omega

theorem core_rank_of_target_det_ne_zero {n q : ℕ}
    (M : Square n) (R J : Fin (q + 2) → Fin n)
    (hdet : minor M R J ≠ 0) :
    (M.submatrix R (J ∘ middleIndices)).rank = q := by
  have hli := (Matrix.linearIndependent_cols_of_det_ne_zero hdet).comp
    middleIndices strictMono_middleIndices.injective
  rw [Matrix.rank_eq_finrank_span_cols]
  change Module.finrank ℝ (Submodule.span ℝ (Set.range ((M.submatrix R J).col ∘ middleIndices))) = q
  have h := linearIndependent_iff_card_eq_finrank_span.mp hli
  simpa only [Set.finrank, Fintype.card_fin] using h.symm

end IV01
