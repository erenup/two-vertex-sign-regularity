import IV01.DeterminantIdentities
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Order.Fin.Tuple

namespace IV01

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The determinant with all but its first row fixed. -/
noncomputable def detConsLinear {q : ℕ}
    (B : Matrix (Fin q) (Fin (q + 1)) R) : (Fin (q + 1) → R) →ₗ[R] R where
  toFun v := Matrix.det (Matrix.of (Matrix.vecCons v B))
  map_add' x y := Matrix.detRowAlternating.toMultilinearMap.cons_add B x y
  map_smul' c x := Matrix.detRowAlternating.toMultilinearMap.cons_smul B c x

/-- Interior columns of a linearly ordered set with `q+3` columns. -/
def feketeInterior {q : ℕ} (j : Fin (q + 1)) : Fin (q + 3) := j.succ.castSucc

/-- The `q` columns shared by all six minors in the three-term identity. -/
def feketeCore {q : ℕ} (b : Fin (q + 1)) (j : Fin q) : Fin (q + 3) :=
  feketeInterior (b.succAbove j)

/-- The core together with the first column, in increasing order. -/
def feketeLeft {q : ℕ} (b : Fin (q + 1)) : Fin (q + 1) → Fin (q + 3) :=
  Fin.cons 0 (feketeCore b)

/-- The core together with the last column, in increasing order. -/
def feketeRight {q : ℕ} (b : Fin (q + 1)) : Fin (q + 1) → Fin (q + 3) :=
  Fin.snoc (feketeCore b) (Fin.last (q + 2))

theorem strictMono_feketeInterior {q : ℕ} : StrictMono (@feketeInterior q) := by
  intro a b h
  change a.val + 1 < b.val + 1
  have hab : a.val < b.val := h
  omega

theorem strictMono_feketeCore {q : ℕ} (b : Fin (q + 1)) : StrictMono (feketeCore b) :=
  strictMono_feketeInterior.comp (Fin.strictMono_succAbove b)

theorem strictMono_feketeLeft {q : ℕ} (b : Fin (q + 1)) : StrictMono (feketeLeft b) := by
  apply Fin.strictMono_cons.mpr
  refine ⟨fun j => ?_, strictMono_feketeCore b⟩
  change 0 < (b.succAbove j).val + 1
  omega

theorem strictMono_feketeRight {q : ℕ} (b : Fin (q + 1)) : StrictMono (feketeRight b) := by
  unfold feketeRight
  rw [← Fin.insertNth_last', Fin.strictMono_insertNth_iff]
  refine ⟨strictMono_feketeCore b, fun j _ => ?_, fun j hj => ?_⟩
  · change (b.succAbove j).val + 1 < q + 2
    have h := (b.succAbove j).isLt
    omega
  · have h := j.isLt
    simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hj
    omega

/-- Exact three-term Fekete identity in increasing column order. A general
ordered union of columns is obtained by restricting its matrix to that union.
No rank hypothesis is required; the row selection need not even be injective. -/
theorem fekete_three_term {q : ℕ}
    (A : Matrix (Fin (q + 2)) (Fin (q + 3)) R)
    (rows : Fin (q + 1) → Fin (q + 2)) (b : Fin (q + 1)) :
    (A.submatrix id (feketeInterior b).succAbove).det *
        (A.submatrix rows feketeInterior).det =
      (A.submatrix id Fin.succ).det * (A.submatrix rows (feketeLeft b)).det +
        (A.submatrix id Fin.castSucc).det * (A.submatrix rows (feketeRight b)).det := by
  let V : Fin (q + 1) → (Fin (q + 1) → R) :=
    fun c r => A (rows r) (feketeInterior c)
  let S : Matrix (Fin q) (Fin (q + 1)) R := fun c => V (b.succAbove c)
  let f : (Fin (q + 2) → R) →ₗ[R] R :=
    (detConsLinear S).comp (LinearMap.funLeft R R rows)
  have f_apply (c : Fin (q + 3)) :
      f (A.col c) = (Matrix.of (Matrix.vecCons (fun r => A (rows r) c) S)).det := rfl
  have f_first : f (A.col 0) = (A.submatrix rows (feketeLeft b)).det := by
    rw [f_apply, ← Matrix.det_transpose (A.submatrix rows (feketeLeft b))]
    congr 1
    ext c r
    refine Fin.cases ?_ (fun d => ?_) c <;>
      simp [feketeLeft, feketeCore, S, V, Matrix.transpose_apply]
  have f_middle : f (A.col (feketeInterior b)) =
      (-1 : R) ^ (b : ℕ) * (A.submatrix rows feketeInterior).det := by
    have h := Matrix.detRowAlternating.neg_one_pow_smul_map_insertNth b (V b) S
    have hinsert : b.insertNth (V b) S = V :=
      b.insertNth_self_removeNth V
    rw [hinsert] at h
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
    change (-1 : R) ^ (b : ℕ) * (Matrix.of V).det = _ at h
    have hdet : (Matrix.of V).det = (A.submatrix rows feketeInterior).det := by
      rw [← Matrix.det_transpose (A.submatrix rows feketeInterior)]
      rfl
    calc
      f (A.col (feketeInterior b)) = Matrix.detRowAlternating (Matrix.vecCons (V b) S) := rfl
      _ = (-1 : R) ^ (b : ℕ) * (Matrix.of V).det := h.symm
      _ = _ := by rw [hdet]
  have f_last : f (A.col (Fin.last (q + 2))) =
      (-1 : R) ^ q * (A.submatrix rows (feketeRight b)).det := by
    have h := Matrix.detRowAlternating.neg_one_pow_smul_map_insertNth
      (Fin.last q) (fun r => A (rows r) (Fin.last (q + 2))) S
    rw [Fin.insertNth_last'] at h
    simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] at h
    change (-1 : R) ^ q * (Matrix.of (Fin.snoc S _)).det = _ at h
    have hdet : (Matrix.of (Fin.snoc S
        (fun r => A (rows r) (Fin.last (q + 2))))).det =
        (A.submatrix rows (feketeRight b)).det := by
      rw [← Matrix.det_transpose (A.submatrix rows (feketeRight b))]
      congr 1
      ext c r
      refine Fin.lastCases ?_ (fun d => ?_) c <;>
        simp [feketeRight, feketeCore, S, V, Matrix.transpose_apply]
    calc
      f (A.col (Fin.last (q + 2))) = Matrix.detRowAlternating
        (Matrix.vecCons (fun r => A (rows r) (Fin.last (q + 2))) S) := rfl
      _ = (-1 : R) ^ q * (Matrix.of (Fin.snoc S _)).det := h.symm
      _ = _ := by rw [hdet]
  have f_core (c : Fin (q + 1)) (hc : c ≠ b) : f (A.col (feketeInterior c)) = 0 := by
    obtain ⟨d, hd⟩ := Fin.exists_succAbove_eq hc
    rw [← hd, f_apply]
    apply Matrix.det_zero_of_row_eq (Fin.succ_ne_zero d).symm
    rfl
  let term (c : Fin (q + 3)) : R :=
    ((-1 : R) ^ (c : ℕ) * (A.submatrix id c.succAbove).det) * f (A.col c)
  have hsum := cofactor_kernel_linear A f
  change (∑ c, term c) = 0 at hsum
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
  have hinterior : (∑ c : Fin (q + 1), term c.castSucc.succ) =
      term (feketeInterior b) := by
    rw [Finset.sum_eq_single b]
    · rfl
    · intro c _ hc
      dsimp [term]
      rw [show c.castSucc.succ = feketeInterior c from rfl, f_core c hc, mul_zero]
    · simp
  rw [hinterior] at hsum
  have hpow (s : ℕ) : (-1 : R) ^ s * (-1 : R) ^ s = 1 := by
    rw [← mul_pow]
    simp
  have hfirst : term 0 =
      (A.submatrix id Fin.succ).det * (A.submatrix rows (feketeLeft b)).det := by
    simp [term, f_first]
  have hmiddle : term (feketeInterior b) =
      -((A.submatrix id (feketeInterior b).succAbove).det *
        (A.submatrix rows feketeInterior).det) := by
    dsimp [term]
    rw [f_middle]
    change ((-1 : R) ^ ((b : ℕ) + 1) * _) * ((-1 : R) ^ (b : ℕ) * _) = _
    rw [pow_succ]
    linear_combination -(A.submatrix id (feketeInterior b).succAbove).det *
      (A.submatrix rows feketeInterior).det * hpow b
  have hlast : term (Fin.last (q + 1)).succ =
      (A.submatrix id Fin.castSucc).det * (A.submatrix rows (feketeRight b)).det := by
    have he : (Fin.last (q + 1)).succ = (Fin.last (q + 2)) := rfl
    rw [he]
    dsimp [term]
    rw [f_last]
    simp only [Fin.succAbove_last, pow_succ]
    linear_combination (A.submatrix id Fin.castSucc).det *
      (A.submatrix rows (feketeRight b)).det * hpow q
  rw [hfirst, hmiddle, hlast] at hsum
  linear_combination -hsum

/-- Fekete's identity inside any ambient matrix. If `rs`, `cs`, and `rows` are
strictly increasing, every displayed minor has its increasing row and column order. -/
theorem fekete_three_term_submatrix {m n : Type*} {q : ℕ}
    (A : Matrix m n R) (rs : Fin (q + 2) → m) (cs : Fin (q + 3) → n)
    (rows : Fin (q + 1) → Fin (q + 2)) (b : Fin (q + 1)) :
    (A.submatrix rs (cs ∘ (feketeInterior b).succAbove)).det *
        (A.submatrix (rs ∘ rows) (cs ∘ feketeInterior)).det =
      (A.submatrix rs (cs ∘ Fin.succ)).det *
          (A.submatrix (rs ∘ rows) (cs ∘ feketeLeft b)).det +
        (A.submatrix rs (cs ∘ Fin.castSucc)).det *
          (A.submatrix (rs ∘ rows) (cs ∘ feketeRight b)).det := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id] using
    fekete_three_term (A.submatrix rs cs) rows b

end IV01
