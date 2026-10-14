import IV01.SchurAlgebra
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace IV01

open Matrix

noncomputable def blockDiagonalRangeEquiv {m n r c : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : Matrix (Fin r) (Fin c) ℝ) :
    LinearMap.range (Matrix.fromBlocks A 0 0 D).mulVecLin ≃ₗ[ℝ]
      (LinearMap.range A.mulVecLin × LinearMap.range D.mulVecLin) where
  toFun x :=
    (⟨x.val ∘ Sum.inl, by
      obtain ⟨v, hv⟩ := x.property
      refine ⟨v ∘ Sum.inl, ?_⟩
      rw [← hv]
      funext i
      simp [Matrix.fromBlocks_mulVec]⟩,
    ⟨x.val ∘ Sum.inr, by
      obtain ⟨v, hv⟩ := x.property
      refine ⟨v ∘ Sum.inr, ?_⟩
      rw [← hv]
      funext i
      simp [Matrix.fromBlocks_mulVec]⟩)
  invFun y := ⟨Sum.elim y.1.val y.2.val, by
    obtain ⟨u, hu⟩ := y.1.property
    obtain ⟨v, hv⟩ := y.2.property
    refine ⟨Sum.elim u v, ?_⟩
    change Matrix.fromBlocks A 0 0 D *ᵥ Sum.elim u v = _
    rw [Matrix.fromBlocks_mulVec]
    simp [Function.comp_def, ← hu, ← hv]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  right_inv x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' x y := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' a x := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem rank_blockDiagonal {m n r c : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : Matrix (Fin r) (Fin c) ℝ) :
    (Matrix.fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  rw [Matrix.rank, (blockDiagonalRangeEquiv A D).finrank_eq, Module.finrank_prod]
  rfl

/-- Rank elimination at an arbitrary invertible pivot block. Both residual
block dimensions may differ, and the pivot may have order zero. -/
theorem rank_fromBlocks_schur {p r c : ℕ} (H : Square p)
    (B : Matrix (Fin p) (Fin c) ℝ) (C : Matrix (Fin r) (Fin p) ℝ)
    (D : Matrix (Fin r) (Fin c) ℝ) (hH : H.det ≠ 0) :
    (Matrix.fromBlocks H B C D).rank = p + (D - C * H⁻¹ * B).rank := by
  let := Matrix.invertibleOfIsUnitDet H (isUnit_iff_ne_zero.mpr hH)
  rw [Matrix.fromBlocks_eq_of_invertible₁₁ H B C D, Matrix.invOf_eq_nonsing_inv]
  have hL : (Matrix.fromBlocks (1 : Square p) (0 : Matrix (Fin p) (Fin r) ℝ)
      (C * H⁻¹) (1 : Square r)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₁₂]
    simp
  have hU : (Matrix.fromBlocks (1 : Square p) (H⁻¹ * B)
      (0 : Matrix (Fin c) (Fin p) ℝ) (1 : Square c)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simp
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hU,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hL, rank_blockDiagonal,
    Matrix.rank_of_det_ne_zero hH]
  simp

lemma appended_submatrix_as_blocks_rect {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n) :
    (M.submatrix (appendIndices P R) (appendIndices Q C)).submatrix
      finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (M.submatrix P Q) (M.submatrix P C)
        (M.submatrix R Q) (M.submatrix R C) := by
  ext i j
  cases i <;> cases j <;>
    simp [appendIndices, Matrix.submatrix_apply, Matrix.fromBlocks]

/-- Equation (4.2) with pivot-first row and column orders. -/
theorem schurAt_rank {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (hH : (M.submatrix P Q).det ≠ 0) :
    (M.submatrix (appendIndices P R) (appendIndices Q C)).rank =
      p + (schurAt M P Q R C).rank := by
  calc
    _ = ((M.submatrix (appendIndices P R) (appendIndices Q C)).submatrix
      finSumFinEquiv finSumFinEquiv).rank :=
        (Matrix.rank_submatrix _ finSumFinEquiv finSumFinEquiv).symm
    _ = _ := by
      rw [appended_submatrix_as_blocks_rect, rank_fromBlocks_schur _ _ _ _ hH]
      rfl

/-- Equation (4.2) in any supplied row and column orders, including sorted
orders. Rank does not acquire the parity factors needed for determinants. -/
theorem schurAt_sorted_rank {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n)
    (Rall : Fin (p + r) → Fin n) (Call : Fin (p + c) → Fin n)
    (σ : Equiv.Perm (Fin (p + r))) (τ : Equiv.Perm (Fin (p + c)))
    (hsortR : appendIndices P R = Rall ∘ σ)
    (hsortC : appendIndices Q C = Call ∘ τ)
    (hH : (M.submatrix P Q).det ≠ 0) :
    (M.submatrix Rall Call).rank = p + (schurAt M P Q R C).rank := by
  have h := schurAt_rank M P Q R C hH
  rw [hsortR, hsortC] at h
  change ((M.submatrix Rall Call).submatrix σ τ).rank = _ at h
  rwa [Matrix.rank_submatrix] at h

lemma pivotSign_ne_zero {n p : ℕ} (P : Fin p → Fin n) (i : Fin n) :
    pivotSign P i ≠ 0 := pow_ne_zero _ (by norm_num)

lemma pivotSign_diagonal_det_ne_zero {n p r : ℕ}
    (P : Fin p → Fin n) (R : Fin r → Fin n) :
    (Matrix.diagonal fun i => pivotSign P (R i)).det ≠ 0 := by
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pivotSign_ne_zero P (R i))

theorem signedSchurAt_rank {n p r c : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R : Fin r → Fin n) (C : Fin c → Fin n) :
    (signedSchurAt M P Q R C).rank = (schurAt M P Q R C).rank := by
  rw [signedSchurAt,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (pivotSign_diagonal_det_ne_zero Q C),
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (pivotSign_diagonal_det_ne_zero P R)]

end IV01
