import IV01.SchurAlgebra
import Mathlib.Data.Finset.Sort

set_option backward.isDefEq.respectTransparency false

namespace IV01

/-- An increasing pivot family has an increasing complementary family of
the expected size, together with the permutation that lists the pivot first. -/
theorem exists_increasing_complement {p m : ℕ}
    (P : Fin p → Fin (p + m)) (hP : Function.Injective P) :
    ∃ R : Fin m → Fin (p + m), StrictMono R ∧
      (∀ i j, P i ≠ R j) ∧
      (∀ x, x ∈ Set.range R ↔ x ∉ Set.range P) ∧
      ∃ σ : Equiv.Perm (Fin (p + m)), appendIndices P R = σ := by
  classical
  let s : Finset (Fin (p + m)) := Finset.univ \ Finset.univ.image P
  have hs : s.card = m := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_image_of_injective _ hP,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    omega
  let R : Fin m ↪o Fin (p + m) := s.orderEmbOfFin hs
  have hRrange : Set.range R = {x | x ∉ Set.range P} := by
    rw [Finset.range_orderEmbOfFin]
    ext x
    simp [s]
  have hdis : ∀ i j, P i ≠ R j := by
    intro i j h
    have hj : R j ∉ Set.range P := by
      change R j ∈ {x | x ∉ Set.range P}
      rw [← hRrange]
      exact ⟨j, rfl⟩
    exact hj ⟨i, h⟩
  have hcomp : ∀ x, x ∈ Set.range R ↔ x ∉ Set.range P := by
    intro x
    rw [hRrange]
    rfl
  have happ : Function.Injective (appendIndices P R) :=
    appendIndices_injective P R hP R.injective hdis
  let σ : Equiv.Perm (Fin (p + m)) :=
    Equiv.ofBijective (appendIndices P R) (Finite.injective_iff_bijective.mp happ)
  exact ⟨R, R.strictMono, hdis, hcomp, σ, rfl⟩

/-- Increasing maps whose images lie in an increasing family's range lift
uniquely to increasing index maps in that family. -/
theorem exists_strictMono_lift {α β γ : Type*}
    [LinearOrder α] [LinearOrder β] [Preorder γ]
    (f : β → α) (hf : StrictMono f) (g : γ → α) (hg : StrictMono g)
    (hmem : ∀ i, g i ∈ Set.range f) :
    ∃ h : γ → β, StrictMono h ∧ f ∘ h = g := by
  classical
  choose h hh using hmem
  refine ⟨h, ?_, funext hh⟩
  intro i j hij
  apply hf.lt_iff_lt.mp
  rw [hh, hh]
  exact hg hij

theorem appendIndices_comp {n p r s : ℕ} (rows : Fin s → Fin n)
    (P : Fin p → Fin s) (R : Fin r → Fin s) :
    appendIndices (rows ∘ P) (rows ∘ R) = rows ∘ appendIndices P R := by
  funext i
  dsimp [appendIndices]
  cases finSumFinEquiv.symm i <;> rfl

/-- Splitting inside a selected increasing family supplies the exact
sorting permutation needed by the signed Schur formulas. -/
theorem exists_complement_inside {n p m : ℕ}
    (rows : Fin (p + m) → Fin n) (hrows : StrictMono rows)
    (P : Fin p → Fin (p + m)) (hP : StrictMono P) :
    ∃ R : Fin m → Fin (p + m), StrictMono R ∧
      (∀ i j, P i ≠ R j) ∧
      (∀ x, x ∈ Set.range R ↔ x ∉ Set.range P) ∧
      ∃ σ : Equiv.Perm (Fin (p + m)),
        appendIndices (rows ∘ P) (rows ∘ R) = rows ∘ σ := by
  obtain ⟨R, hR, hdis, hcomp, σ, hσ⟩ := exists_increasing_complement P hP.injective
  exact ⟨R, hR, hdis, hcomp, σ, by rw [appendIndices_comp, hσ]⟩

end IV01
