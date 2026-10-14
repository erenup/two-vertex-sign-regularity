import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace IV01

open Matrix Module

variable {R : Type*} [Field R]

/-- From any finite generating family whose span has dimension at least `k`,
select `k` linearly independent members. -/
theorem exists_independent_subfamily_of_le_finrank_span
    {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module R V]
    (v : ι → V) (k : ℕ) (hk : k ≤ finrank R (Submodule.span R (Set.range v))) :
    ∃ e : Fin k → ι, Function.Injective e ∧ LinearIndependent R (v ∘ e) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' R v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = finrank R (Submodule.span R (Set.range v)) := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card κ = finrank R (Submodule.span R (Set.range (v ∘ a))) at h
    rw [hspan] at h
    exact h
  obtain ⟨e⟩ : Nonempty (Fin k ↪ κ) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin, hcard] using hk)
  exact ⟨a ∘ e, ha.comp e.injective, hli.comp e e.injective⟩

/-- In an ordered finite index type the independent subfamily can be selected
in increasing index order. -/
theorem exists_strictMono_independent_subfamily_of_le_finrank_span
    {ι V : Type*} [Fintype ι] [LinearOrder ι] [AddCommGroup V] [Module R V]
    (v : ι → V) (k : ℕ) (hk : k ≤ finrank R (Submodule.span R (Set.range v))) :
    ∃ e : Fin k → ι, StrictMono e ∧ LinearIndependent R (v ∘ e) := by
  classical
  obtain ⟨e, he, hli⟩ := exists_independent_subfamily_of_le_finrank_span v k hk
  let s := Finset.univ.image e
  have hs : s.card = k := by
    rw [Finset.card_image_of_injective _ he]
    exact Fintype.card_fin k
  let g : Fin k ↪o ι := s.orderEmbOfFin hs
  have hrg : Set.range g = Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨g, g.strictMono, (linearIndepOn_range_iff g.injective v).mp ?_⟩
  rw [hrg]
  exact (linearIndepOn_range_iff he v).mpr hli

/-- Every rank lower bound is witnessed by a nonsingular square submatrix. -/
theorem exists_nonzero_minor_of_le_rank {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n R) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ (rows : Fin k → m) (cols : Fin k → n),
      Function.Injective rows ∧ Function.Injective cols ∧ (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨cols, hcols, hliCols⟩ := exists_independent_subfamily_of_le_finrank_span A.col k
    (by simpa only [A.rank_eq_finrank_span_cols] using hk)
  let C := A.submatrix id cols
  have hrankC : C.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols]
    change finrank R (Submodule.span R (Set.range (A.col ∘ cols))) = k
    have h := linearIndependent_iff_card_eq_finrank_span.mp hliCols
    simpa only [Fintype.card_fin, Set.finrank] using h.symm
  obtain ⟨rows, hrows, hliRows⟩ := exists_independent_subfamily_of_le_finrank_span C.row k
    (by rw [← Matrix.rank_eq_finrank_span_row, hrankC])
  refine ⟨rows, cols, hrows, hcols, ?_⟩
  have hli : LinearIndependent R (A.submatrix rows cols).row := hliRows
  exact (isUnit_iff_ne_zero.mp
    ((A.submatrix rows cols).isUnit_iff_isUnit_det.mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli)))

/-- Matrix rank equals the largest order of a nonzero minor. -/
theorem le_rank_iff_exists_nonzero_minor {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n R) (k : ℕ) :
    k ≤ A.rank ↔ ∃ (rows : Fin k → m) (cols : Fin k → n),
      Function.Injective rows ∧ Function.Injective cols ∧ (A.submatrix rows cols).det ≠ 0 := by
  refine ⟨exists_nonzero_minor_of_le_rank A k, ?_⟩
  rintro ⟨rows, cols, _, _, hdet⟩
  have hrank := Matrix.rank_of_det_ne_zero hdet
  have hle := A.rank_submatrix_le rows cols
  simpa only [hrank, Fintype.card_fin] using hle

/-- Vanishing of every order-`k` minor forces rank strictly below `k`. -/
theorem rank_lt_of_all_minors_zero {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n R) (k : ℕ)
    (hz : ∀ (rows : Fin k → m) (cols : Fin k → n),
      Function.Injective rows → Function.Injective cols → (A.submatrix rows cols).det = 0) :
    A.rank < k := by
  by_contra h
  obtain ⟨rows, cols, hr, hc, hd⟩ := exists_nonzero_minor_of_le_rank A k (Nat.le_of_not_gt h)
  exact hd (hz rows cols hr hc)

/-- Increasing row and column maps can witness every rank lower bound. -/
theorem exists_nonzero_increasing_minor_of_le_rank
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    (A : Matrix m n R) (k : ℕ) (hk : k ≤ A.rank) :
    ∃ (rows : Fin k → m) (cols : Fin k → n),
      StrictMono rows ∧ StrictMono cols ∧ (A.submatrix rows cols).det ≠ 0 := by
  classical
  obtain ⟨cols, hcols, hliCols⟩ :=
    exists_strictMono_independent_subfamily_of_le_finrank_span A.col k
      (by simpa only [A.rank_eq_finrank_span_cols] using hk)
  let C := A.submatrix id cols
  have hrankC : C.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols]
    change finrank R (Submodule.span R (Set.range (A.col ∘ cols))) = k
    have h := linearIndependent_iff_card_eq_finrank_span.mp hliCols
    simpa only [Fintype.card_fin, Set.finrank] using h.symm
  obtain ⟨rows, hrows, hliRows⟩ :=
    exists_strictMono_independent_subfamily_of_le_finrank_span C.row k
      (by rw [← Matrix.rank_eq_finrank_span_row, hrankC])
  refine ⟨rows, cols, hrows, hcols, ?_⟩
  have hli : LinearIndependent R (A.submatrix rows cols).row := hliRows
  exact isUnit_iff_ne_zero.mp
    ((A.submatrix rows cols).isUnit_iff_isUnit_det.mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hli))

/-- Rank characterized using precisely the increasing-index minor convention. -/
theorem le_rank_iff_exists_nonzero_increasing_minor
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    (A : Matrix m n R) (k : ℕ) :
    k ≤ A.rank ↔ ∃ (rows : Fin k → m) (cols : Fin k → n),
      StrictMono rows ∧ StrictMono cols ∧ (A.submatrix rows cols).det ≠ 0 := by
  refine ⟨exists_nonzero_increasing_minor_of_le_rank A k, ?_⟩
  rintro ⟨rows, cols, hr, hc, hd⟩
  exact (le_rank_iff_exists_nonzero_minor A k).mpr ⟨rows, cols, hr.injective, hc.injective, hd⟩

/-- A rank bound is equivalent to vanishing of all increasing minors of the
next order, including when that order exceeds the available row or column count. -/
theorem rank_le_iff_all_increasing_minors_zero
    {m n : Type*} [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n]
    (A : Matrix m n R) (r : ℕ) :
    A.rank ≤ r ↔ ∀ (rows : Fin (r + 1) → m) (cols : Fin (r + 1) → n),
      StrictMono rows → StrictMono cols → (A.submatrix rows cols).det = 0 := by
  constructor
  · intro h rows cols hr hc
    by_contra hd
    have hk := (le_rank_iff_exists_nonzero_increasing_minor A (r + 1)).mpr
      ⟨rows, cols, hr, hc, hd⟩
    omega
  · intro hz
    by_contra h
    obtain ⟨rows, cols, hr, hc, hd⟩ :=
      exists_nonzero_increasing_minor_of_le_rank A (r + 1) (Nat.lt_of_not_ge h)
    exact hd (hz rows cols hr hc)

end IV01
