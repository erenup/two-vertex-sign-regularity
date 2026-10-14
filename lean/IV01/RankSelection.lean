import IV01.RankBounds

namespace IV01

open Matrix

variable {R : Type*} [Field R]

/-- Every injective family of columns of an invertible matrix has full column rank. -/
theorem rank_submatrix_cols_of_det_ne_zero
    {n q : Type*} [Fintype n] [Fintype q] [DecidableEq n]
    (A : Matrix n n R) (hA : A.det ≠ 0)
    (cols : q → n) (hcols : Function.Injective cols) :
    (A.submatrix id cols).rank = Fintype.card q := by
  have h := rank_add_card_le_rank_submatrix_cols_add_card A cols hcols
  rw [Matrix.rank_of_det_ne_zero hA] at h
  have hu := (A.submatrix id cols).rank_le_card_width
  omega

/-- Every injective family of rows of an invertible matrix has full row rank. -/
theorem rank_submatrix_rows_of_det_ne_zero
    {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n]
    (A : Matrix n n R) (hA : A.det ≠ 0)
    (rows : p → n) (hrows : Function.Injective rows) :
    (A.submatrix rows id).rank = Fintype.card p := by
  have h := rank_add_card_le_rank_submatrix_rows_add_card A rows hrows
  rw [Matrix.rank_of_det_ne_zero hA] at h
  have hu := (A.submatrix rows id).rank_le_card_height
  omega

/-- Selecting any distinct columns of a nonzero square minor gives full column rank. -/
theorem rank_selected_columns_of_minor_ne_zero
    {m n k q : Type*} [Fintype k] [Fintype q] [DecidableEq k]
    (A : Matrix m n R) (rows : k → m) (cols : k → n)
    (hA : (A.submatrix rows cols).det ≠ 0)
    (selected : q → k) (hselected : Function.Injective selected) :
    (A.submatrix rows (cols ∘ selected)).rank = Fintype.card q := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id] using
    rank_submatrix_cols_of_det_ne_zero (A.submatrix rows cols) hA selected hselected

/-- Selecting any distinct rows of a nonzero square minor gives full row rank. -/
theorem rank_selected_rows_of_minor_ne_zero
    {m n k p : Type*} [Fintype k] [Fintype p] [DecidableEq k]
    (A : Matrix m n R) (rows : k → m) (cols : k → n)
    (hA : (A.submatrix rows cols).det ≠ 0)
    (selected : p → k) (hselected : Function.Injective selected) :
    (A.submatrix (rows ∘ selected) cols).rank = Fintype.card p := by
  simpa only [Matrix.submatrix_submatrix, Function.comp_id] using
    rank_submatrix_rows_of_det_ne_zero (A.submatrix rows cols) hA selected hselected

end IV01
