import IV01.InteriorZero
import IV01.InverseInterval
import IV01.Box
import Mathlib.Data.Matrix.Basis

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem monotone_on_scalar_box {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {l u : ι → ℝ}
    (hcoord : ∀ x, ScalarBox l u x → ∀ i a b,
      l i ≤ a ∧ a ≤ u i → l i ≤ b ∧ b ≤ u i → a ≤ b →
      f (Function.update x i a) ≤ f (Function.update x i b))
    {x y : ι → ℝ} (hx : ScalarBox l u x) (hy : ScalarBox l u y)
    (hxy : ∀ i, x i ≤ y i) : f x ≤ f y := by
  let replace (s : Finset ι) : ι → ℝ := fun i => if i ∈ s then y i else x i
  have hbox (s : Finset ι) : ScalarBox l u (replace s) := by
    intro i
    dsimp [replace]
    split_ifs <;> first | exact hy i | exact hx i
  have hle (s : Finset ι) : f x ≤ f (replace s) := by
    induction s using Finset.induction_on with
    | empty => simp [replace]
    | @insert i s hi ih =>
      have heq : replace (insert i s) = Function.update (replace s) i (y i) := by
        funext j
        by_cases hj : j = i <;> simp [replace, hj]
      rw [heq]
      apply ih.trans
      have h := hcoord (replace s) (hbox s) i (x i) (y i) (hx i) (hy i) (hxy i)
      have hxrep : x i = replace s i := by simp [replace, hi]
      simpa only [hxrep, Function.update_eq_self] using h
  simpa [replace] using hle Finset.univ

theorem checkerConjugate_involutive {n : ℕ} (M : Square n) :
    checkerConjugate (checkerConjugate M) = M := by
  ext i j
  simp only [checkerConjugate_apply]
  rcases neg_one_pow_eq_or ℝ (i.val + j.val) with h | h <;> simp [h]

theorem det_add_single {n : ℕ} (A : Square n) (i j : Fin n) (t : ℝ) :
    (A + Matrix.single i j t).det = A.det + t * A.adjugate j i := by
  have heq : A + Matrix.single i j t = A.updateRow i (A i + t • Pi.single j 1) := by
    ext r c
    by_cases hr : r = i <;> by_cases hc : c = j <;>
      simp [hr, hc, Matrix.updateRow_apply, Ne.symm]
  rw [heq, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    ← Matrix.adjugate_apply]

theorem checker_coordinate_det_affine {n : ℕ}
    (x : (Fin (n + 1) × Fin (n + 1)) → ℝ) (i j : Fin (n + 1)) (t : ℝ) :
    (checkerConjugate (Function.curry (Function.update x (i, j) t))).det =
      (checkerConjugate (Function.curry x)).det +
        (t - x (i, j)) *
          ((checkerConjugate (Function.curry x)).submatrix i.succAbove j.succAbove).det := by
  let A := checkerConjugate (Function.curry x)
  let s : ℝ := (-1) ^ (i.val + j.val)
  have hs : s * s = 1 := by
    rcases neg_one_pow_eq_or ℝ (i.val + j.val) with h | h <;> simp [s, h]
  have heq : checkerConjugate (Function.curry (Function.update x (i, j) t)) =
      A + Matrix.single i j (s * (t - x (i, j))) := by
    ext r c
    by_cases hr : r = i <;> by_cases hc : c = j <;>
      simp [A, checkerConjugate_apply, Function.curry, Function.update_apply, hr, hc, s,
        Ne.symm] <;> ring
  rw [heq, det_add_single, Matrix.adjugate_fin_succ_eq_det_submatrix]
  change A.det + s * (t - x (i, j)) * (s * (A.submatrix i.succAbove j.succAbove).det) = _
  calc
    _ = A.det + (s * s) * ((t - x (i, j)) *
        (A.submatrix i.succAbove j.succAbove).det) := by ring
    _ = _ := by rw [hs, one_mul]

/-- Cofactors of one common weak sign make the determinant monotone in
the checker coordinates. No nonsingularity is needed. -/
theorem checker_det_monotone {n : ℕ} (s : ℝ)
    {l u : (Fin (n + 1) × Fin (n + 1)) → ℝ}
    (hcofactor : ∀ x, ScalarBox l u x → ∀ i j : Fin (n + 1),
      0 ≤ s * ((checkerConjugate (Function.curry x)).submatrix i.succAbove j.succAbove).det)
    {x y : (Fin (n + 1) × Fin (n + 1)) → ℝ}
    (hx : ScalarBox l u x) (hy : ScalarBox l u y) (hxy : ∀ ij, x ij ≤ y ij) :
    s * (checkerConjugate (Function.curry x)).det ≤
      s * (checkerConjugate (Function.curry y)).det := by
  apply monotone_on_scalar_box (f := fun z => s * (checkerConjugate (Function.curry z)).det)
    (l := l) (u := u) ?_ hx hy hxy
  intro z hz ij a b _ _ hab
  change s * (checkerConjugate (Function.curry (Function.update z ij a))).det ≤
    s * (checkerConjugate (Function.curry (Function.update z ij b))).det
  rw [checker_coordinate_det_affine, checker_coordinate_det_affine]
  have hp := mul_nonneg (sub_nonneg.mpr hab) (hcofactor z hz ij.1 ij.2)
  nlinarith

theorem inBox_of_checker_bounds {n : ℕ} {L U X : Square n}
    (h : EntrywiseLE (checkerConjugate (checkerMinus L U)) (checkerConjugate X) ∧
      EntrywiseLE (checkerConjugate X) (checkerConjugate (checkerPlus L U))) :
    InBox L U X := by
  constructor <;> intro i j
  · have hm := h.1 i j
    have hp := h.2 i j
    simp only [checkerConjugate_apply, checker_sign_eq, checkerMinus, checkerPlus] at hm hp
    split_ifs at hm hp <;> simp only [one_mul, neg_one_mul, neg_le_neg_iff] at hm hp <;> assumption
  · have hm := h.1 i j
    have hp := h.2 i j
    simp only [checkerConjugate_apply, checker_sign_eq, checkerMinus, checkerPlus] at hm hp
    split_ifs at hm hp <;> simp only [one_mul, neg_one_mul, neg_le_neg_iff] at hm hp <;> assumption

theorem checker_determinant_bounds {n : ℕ} {L U M : Square (n + 1)}
    (hLU : EntrywiseLE L U) (s : ℝ)
    (hcofactor : ∀ X, InBox L U X → ∀ i j : Fin (n + 1),
      0 ≤ s * (X.submatrix i.succAbove j.succAbove).det)
    (hM : InBox L U M) :
    s * (checkerMinus L U).det ≤ s * M.det ∧
      s * M.det ≤ s * (checkerPlus L U).det := by
  let l := Function.uncurry (checkerConjugate (checkerMinus L U))
  let u := Function.uncurry (checkerConjugate (checkerPlus L U))
  let x := Function.uncurry (checkerConjugate M)
  have hx : ScalarBox l u x := by
    have h := checkerConjugate_box_bounds hM
    exact fun ij => ⟨h.1 ij.1 ij.2, h.2 ij.1 ij.2⟩
  have hlu : ∀ ij, l ij ≤ u ij := fun ij => (hx ij).1.trans (hx ij).2
  have hl : ScalarBox l u l := fun ij => ⟨le_rfl, hlu ij⟩
  have hu : ScalarBox l u u := fun ij => ⟨hlu ij, le_rfl⟩
  have hcf : ∀ z, ScalarBox l u z → ∀ i j : Fin (n + 1),
      0 ≤ s * ((checkerConjugate (Function.curry z)).submatrix i.succAbove j.succAbove).det := by
    intro z hz i j
    apply hcofactor _ ?_ i j
    apply inBox_of_checker_bounds
    rw [checkerConjugate_involutive]
    exact ⟨fun a b => (hz (a, b)).1, fun a b => (hz (a, b)).2⟩
  have hlo := checker_det_monotone s hcf hl hx (fun ij => (hx ij).1)
  have hhi := checker_det_monotone s hcf hx hu (fun ij => (hx ij).2)
  constructor
  · simpa [l, x, Function.curry_uncurry, checkerConjugate_involutive] using hlo
  · simpa [u, x, Function.curry_uncurry, checkerConjugate_involutive] using hhi

theorem mul_nonneg_of_between {a x b t : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (ha : 0 ≤ t * a) (hb : 0 ≤ t * b) :
    0 ≤ t * x := by
  by_cases ht : 0 ≤ t
  · exact ha.trans (mul_le_mul_of_nonneg_left hax ht)
  · exact hb.trans (mul_le_mul_of_nonpos_left hxb (le_of_not_ge ht))

/-- A determinant with correctly signed cofactors throughout a box has
the sign shared by the two checker endpoint determinants. -/
theorem determinant_sign_of_checker_endpoints {n : ℕ} {L U M : Square (n + 1)}
    (hLU : EntrywiseLE L U) (s t : ℝ) (hs : s = 1 ∨ s = -1)
    (hcofactor : ∀ X, InBox L U X → ∀ i j : Fin (n + 1),
      0 ≤ s * (X.submatrix i.succAbove j.succAbove).det)
    (ha : 0 ≤ t * (checkerMinus L U).det)
    (hb : 0 ≤ t * (checkerPlus L U).det)
    (hM : InBox L U M) : 0 ≤ t * M.det := by
  obtain ⟨hlo, hhi⟩ := checker_determinant_bounds hLU s hcofactor hM
  rcases hs with h | h
  · simp only [h, one_mul] at hlo hhi
    exact mul_nonneg_of_between hlo hhi ha hb
  · simp only [h, neg_one_mul, neg_le_neg_iff] at hlo hhi
    exact mul_nonneg_of_between hhi hlo hb ha

end IV01
