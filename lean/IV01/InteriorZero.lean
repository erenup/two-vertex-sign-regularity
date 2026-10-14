import IV01.Definitions
import Mathlib.Tactic

/-! Interior-zero rigidity for coordinatewise affine functions on finite boxes. -/

namespace IV01

def CoordinateAffine {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ x i, ∃ a b : ℝ, ∀ t : ℝ, f (Function.update x i t) = a * t + b

def ScalarBox {ι : Type*} (l u x : ι → ℝ) : Prop :=
  ∀ i, l i ≤ x i ∧ x i ≤ u i

def RelativeInteriorBox {ι : Type*} (l u x : ι → ℝ) : Prop :=
  ScalarBox l u x ∧ ∀ i, l i < u i → l i < x i ∧ x i < u i

theorem affine_zero_of_nonneg_of_interior_zero
    {l u x a b : ℝ} (hlx : l < x) (hxu : x < u)
    (hl : 0 ≤ a * l + b) (hu : 0 ≤ a * u + b) (hx : a * x + b = 0) :
    a = 0 ∧ b = 0 := by
  have hal : 0 ≤ a * (l - x) := by nlinarith
  have hau : 0 ≤ a * (u - x) := by nlinarith
  have ha₁ : a ≤ 0 := by
    by_contra h
    have : a * (l - x) < 0 := mul_neg_of_pos_of_neg (lt_of_not_ge h) (sub_neg.mpr hlx)
    linarith
  have ha₂ : 0 ≤ a := by
    by_contra h
    have : a * (u - x) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge h) (sub_pos.mpr hxu)
    linarith
  have ha : a = 0 := le_antisymm ha₁ ha₂
  exact ⟨ha, by simpa [ha] using hx⟩

theorem ScalarBox.update {ι : Type*} [DecidableEq ι]
    {l u x : ι → ℝ} (hx : ScalarBox l u x) (i : ι) {t : ℝ}
    (ht : l i ≤ t ∧ t ≤ u i) : ScalarBox l u (Function.update x i t) := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne h] using hx j

theorem CoordinateAffine.zero_update
    {ι : Type*} [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : CoordinateAffine f) {l u x : ι → ℝ}
    (hnonneg : ∀ y, ScalarBox l u y → 0 ≤ f y)
    (hx : ScalarBox l u x) (hzero : f x = 0)
    (i : ι) (hi : l i < u i → l i < x i ∧ x i < u i)
    {t : ℝ} (ht : l i ≤ t ∧ t ≤ u i) :
    f (Function.update x i t) = 0 := by
  obtain ⟨a, b, hab⟩ := hf x i
  by_cases hlu : l i < u i
  · have hz : a * x i + b = 0 := by
      rw [← hab]
      simpa using hzero
    have hl : 0 ≤ a * l i + b := by
      rw [← hab]
      exact hnonneg _ (hx.update i ⟨le_rfl, hlu.le⟩)
    have hu : 0 ≤ a * u i + b := by
      rw [← hab]
      exact hnonneg _ (hx.update i ⟨hlu.le, le_rfl⟩)
    obtain ⟨ha, hb⟩ := affine_zero_of_nonneg_of_interior_zero (hi hlu).1 (hi hlu).2 hl hu hz
    simp [hab, ha, hb]
  · have htx : t = x i := by have := hx i; linarith
    simpa [htx] using hzero

/-- A coordinatewise affine function nonnegative on a finite box vanishes
everywhere if it vanishes at one relative-interior point. Fixed coordinates
are allowed, and no full-dimensionality hypothesis is imposed. -/
theorem CoordinateAffine.zero_on_box
    {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : CoordinateAffine f) {l u x : ι → ℝ}
    (hnonneg : ∀ y, ScalarBox l u y → 0 ≤ f y)
    (hx : RelativeInteriorBox l u x) (hzero : f x = 0) :
    ∀ y, ScalarBox l u y → f y = 0 := by
  intro y hy
  let replace (s : Finset ι) : ι → ℝ := fun i => if i ∈ s then y i else x i
  have hbox (s : Finset ι) : ScalarBox l u (replace s) := by
    intro i
    dsimp [replace]
    split_ifs <;> first | exact hy i | exact hx.1 i
  have hz (s : Finset ι) : f (replace s) = 0 := by
    induction s using Finset.induction_on with
    | empty => simpa [replace] using hzero
    | @insert i s hi ih =>
      have heq : replace (insert i s) = Function.update (replace s) i (y i) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [replace]
        · simp [replace, hj]
      rw [heq]
      apply hf.zero_update hnonneg (hbox s) ih i _ (hy i)
      simpa [replace, hi] using hx.2 i
  simpa [replace] using hz Finset.univ

theorem CoordinateAffine.mul_const
    {ι : Type*} [DecidableEq ι] {f : (ι → ℝ) → ℝ}
    (hf : CoordinateAffine f) (c : ℝ) : CoordinateAffine (fun x => c * f x) := by
  intro x i
  obtain ⟨a, b, hab⟩ := hf x i
  refine ⟨c * a, c * b, fun t => ?_⟩
  dsimp only
  rw [hab]
  ring

theorem CoordinateAffine.comp_injective
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {f : (κ → ℝ) → ℝ} (hf : CoordinateAffine f)
    (e : κ → ι) (he : Function.Injective e) :
    CoordinateAffine (fun x => f (x ∘ e)) := by
  intro x i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hi
    obtain ⟨a, b, hab⟩ := hf (x ∘ e) j
    refine ⟨a, b, fun t => ?_⟩
    dsimp only
    rw [Function.update_comp_eq_of_injective x he]
    exact hab t
  · refine ⟨0, f (x ∘ e), fun t => ?_⟩
    dsimp only
    rw [Function.update_comp_eq_of_forall_ne x t (fun j hj => hi ⟨j, hj⟩)]
    simp

/-- Determinants are affine in each individual matrix entry. -/
theorem determinant_coordinateAffine
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    CoordinateAffine (fun x : (ι × ι) → ℝ => Matrix.det (fun i j => x (i, j))) := by
  intro x ij
  rcases ij with ⟨i, j⟩
  let M : Matrix ι ι ℝ := fun r c => x (r, c)
  let u : ι → ℝ := Function.update (M i) j 0
  let v : ι → ℝ := fun c => if c = j then 1 else 0
  refine ⟨Matrix.det (M.updateRow i v), Matrix.det (M.updateRow i u), fun t => ?_⟩
  dsimp only
  have heq : (fun r c => Function.update x (i, j) t (r, c)) =
      M.updateRow i (u + t • v) := by
    ext r c
    by_cases hr : r = i <;> by_cases hc : c = j <;>
      simp [M, u, v, Matrix.updateRow, Function.update_apply, hr, hc]
  rw [heq, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  ring

theorem minor_coordinateAffine {n k : ℕ} (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols) :
    CoordinateAffine (fun x : (Fin n × Fin n) → ℝ =>
      minor (fun i j => x (i, j)) rows cols) := by
  let e : Fin k × Fin k → Fin n × Fin n := fun ij => (rows ij.1, cols ij.2)
  have he : Function.Injective e := by
    intro x y h
    exact Prod.ext (hr (congrArg Prod.fst h)) (hc (congrArg Prod.snd h))
  exact determinant_coordinateAffine.comp_injective e he

def InRelativeInterior {n : ℕ} (L U M : Square n) : Prop :=
  InBox L U M ∧ ∀ i j, L i j < U i j → L i j < M i j ∧ M i j < U i j

/-- Section 5.1 of the written proof, for any specified signed minor. -/
theorem signed_minor_zero_on_box {n k : ℕ} {L U M : Square n}
    (rows cols : Fin k → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (s : ℝ) (hnonneg : ∀ X, InBox L U X → 0 ≤ s * minor X rows cols)
    (hM : InRelativeInterior L U M) (hz : s * minor M rows cols = 0)
    {X : Square n} (hX : InBox L U X) : s * minor X rows cols = 0 := by
  refine ((minor_coordinateAffine rows cols hr.injective hc.injective).mul_const s).zero_on_box
    (l := Function.uncurry L) (u := Function.uncurry U) (x := Function.uncurry M)
    ?_ ?_ hz (Function.uncurry X) ?_
  · intro y hy
    apply hnonneg (Function.curry y)
    exact ⟨fun i j => (hy (i, j)).1, fun i j => (hy (i, j)).2⟩
  · exact ⟨fun ij => ⟨hM.1.1 ij.1 ij.2, hM.1.2 ij.1 ij.2⟩,
      fun ij => hM.2 ij.1 ij.2⟩
  · exact fun ij => ⟨hX.1 ij.1 ij.2, hX.2 ij.1 ij.2⟩

theorem minor_zero_on_box {n k : ℕ} {L U M : Square n}
    (rows cols : Fin k → Fin n) (hr : StrictMono rows) (hc : StrictMono cols)
    (s : ℝ) (hs : s ≠ 0) (hnonneg : ∀ X, InBox L U X → 0 ≤ s * minor X rows cols)
    (hM : InRelativeInterior L U M) (hz : minor M rows cols = 0)
    {X : Square n} (hX : InBox L U X) : minor X rows cols = 0 := by
  have := signed_minor_zero_on_box rows cols hr hc s hnonneg hM (by rw [hz, mul_zero]) hX
  exact (mul_eq_zero.mp this).resolve_left hs

end IV01
