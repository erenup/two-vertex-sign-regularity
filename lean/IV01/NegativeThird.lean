import IV01.ColumnCompletion
import IV01.RankRestriction
import IV01.PivotIndices
import IV01.Corner
import IV01.MinimalBad
import IV01.Box

namespace IV01

open Matrix Module

/-- A nonsingular ambient matrix permits constrained column completion on
any selected row family, followed by an increasing nonsingular pivot. -/
theorem exists_pivot_cover_on_rows {n p : ℕ} {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (M : Square n) (rows : α → Fin n) (cols : β → Fin n)
    (hrows : StrictMono rows) (hM : M.det ≠ 0)
    (hp : p ≤ Fintype.card α) (hrank : (M.submatrix rows cols).rank ≤ p) :
    ∃ (I : Fin p → α) (Q : Fin p → Fin n), StrictMono I ∧ StrictMono Q ∧
      (M.submatrix (rows ∘ I) Q).det ≠ 0 ∧
      finrank ℝ (Submodule.span ℝ (Set.range ((M.submatrix rows id).col ∘ Q))) = p ∧
      ∀ j, (M.submatrix rows id).col (cols j) ∈
        Submodule.span ℝ (Set.range ((M.submatrix rows id).col ∘ Q)) := by
  classical
  let A := M.submatrix rows id
  have hfull : A.rank = Fintype.card α := by
    apply LinearIndependent.rank_matrix
    exact (Matrix.linearIndependent_rows_of_det_ne_zero hM).comp rows hrows.injective
  obtain ⟨Q, hQ, hliQ, hcover⟩ := exists_increasing_independent_cover A.col
    (Set.range cols) p (by
      rw [← Set.range_comp]
      exact (Matrix.rank_eq_finrank_span_cols (M.submatrix rows cols)) ▸ hrank)
    (by rw [← Matrix.rank_eq_finrank_span_cols, hfull]; exact hp)
  let C := A.submatrix id Q
  have hdim : finrank ℝ (Submodule.span ℝ (Set.range (A.col ∘ Q))) = p := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hliQ
    simpa only [Fintype.card_fin, Set.finrank] using h.symm
  have hrankC : C.rank = p := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact hdim
  obtain ⟨I, hI, hliI⟩ := exists_strictMono_independent_subfamily_of_le_finrank_span
    C.row p (by rw [← Matrix.rank_eq_finrank_span_row, hrankC])
  have hdet : (M.submatrix (rows ∘ I) Q).det ≠ 0 := by
    exact isUnit_iff_ne_zero.mp ((M.submatrix (rows ∘ I) Q).isUnit_iff_isUnit_det.mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hliI))
  exact ⟨I, Q, hI, hQ, hdet, hdim, fun j => hcover (cols j) ⟨j, rfl⟩⟩

/-- Every covered column gives a zero Schur entry on each source row.
The rank argument allows repeated indices in the auxiliary bordered block. -/
theorem schurAt_entry_zero_of_cover {n p m : ℕ} {α : Type*} [Fintype α]
    (M : Square n) (rows : α → Fin n) (I : Fin p → α) (Q : Fin p → Fin n)
    (R C : Fin m → Fin n) (a : α) (b : Fin n) (i j : Fin m)
    (hi : R i = rows a) (hj : C j = b)
    (hH : (M.submatrix (rows ∘ I) Q).det ≠ 0)
    (hdim : finrank ℝ (Submodule.span ℝ
      (Set.range ((M.submatrix rows id).col ∘ Q))) = p)
    (hcover : (M.submatrix rows id).col b ∈
      Submodule.span ℝ (Set.range ((M.submatrix rows id).col ∘ Q))) :
    schurAt M (rows ∘ I) Q R C i j = 0 := by
  let A := M.submatrix rows id
  let D := A.submatrix id (appendIndices Q (fun _ : Fin 1 => b))
  have hD : D.rank ≤ p := by
    rw [Matrix.rank_eq_finrank_span_cols]
    apply le_of_le_of_eq _ hdim
    apply Submodule.finrank_mono
    apply Submodule.span_le.mpr
    rintro v ⟨k, rfl⟩
    change A.col (Sum.elim Q (fun _ : Fin 1 => b) (finSumFinEquiv.symm k)) ∈ _
    cases finSumFinEquiv.symm k with
    | inl q => exact Submodule.subset_span ⟨q, rfl⟩
    | inr c => exact hcover
  let rr : Fin (p + 1) → α := fun k =>
    Sum.elim I (fun _ : Fin 1 => a) (finSumFinEquiv.symm k)
  have hblock : (M.submatrix (appendIndices (rows ∘ I) (fun _ : Fin 1 => rows a))
      (appendIndices Q (fun _ : Fin 1 => b))).rank ≤ p := by
    have hle := (D.rank_submatrix_le rr id).trans hD
    have heq : D.submatrix rr id =
        M.submatrix (appendIndices (rows ∘ I) (fun _ : Fin 1 => rows a))
          (appendIndices Q (fun _ : Fin 1 => b)) := by
      ext k l
      dsimp [D, A, rr, appendIndices]
      cases finSumFinEquiv.symm k <;> rfl
    rwa [heq] at hle
  have hz := schurAt_eq_zero_of_rank_bound M (rows ∘ I) Q
    (fun _ : Fin 1 => rows a) (fun _ : Fin 1 => b) hH hblock
  have hzentry := congrFun (congrFun hz 0) 0
  change schurAt M (rows ∘ I) Q (fun _ : Fin 1 => rows a)
    (fun _ : Fin 1 => b) 0 0 = 0 at hzentry
  simpa only [schurAt, Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.mul_apply, hi, hj] using hzentry

/-- Removing at most `p` selected ambient indices leaves at least the
original family size minus `p`. -/
lemma card_avoiding_range_ge_sub {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    {p : ℕ} (f : α → ι) (hf : Function.Injective f) (g : Fin p → ι) :
    Fintype.card α - p ≤ Fintype.card {a : α // f a ∉ Set.range g} := by
  classical
  have hremoved : Fintype.card {a : α // f a ∈ Set.range g} ≤ p := by
    choose h hh using (fun a : {a : α // f a ∈ Set.range g} => a.property)
    have hhinj : Function.Injective h := by
      intro a b hab
      apply Subtype.ext
      apply hf
      rw [← hh a, ← hh b, hab]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective h hhinj
  rw [Fintype.card_subtype_compl]
  omega

lemma card_zero_entries_ge_rectangle {m : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (Y : Square m)
    (f : α → Fin m) (g : β → Fin m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hz : ∀ a b, Y (f a) (g b) = 0) :
    Fintype.card α * Fintype.card β ≤
      (Finset.univ.filter (fun ij : Fin m × Fin m => Y ij.1 ij.2 = 0)).card := by
  classical
  let s := Finset.univ.filter (fun ij : Fin m × Fin m => Y ij.1 ij.2 = 0)
  let z : α × β → s := fun ab => ⟨(f ab.1, g ab.2), by simp [s, hz]⟩
  have hinj : Function.Injective z := by
    intro a b hab
    have hh : (f a.1, g a.2) = (f b.1, g b.2) := congrArg Subtype.val hab
    exact Prod.ext (hf (congrArg Prod.fst hh)) (hg (congrArg Prod.snd hh))
  simpa only [Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_le_of_injective z hinj

lemma normalizedSchur_zero_of_schur_zero {n p m : ℕ} (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin m → Fin n) (e e₁ e₂ : ℝ)
    (i j : Fin m) (hz : schurAt M P Q R C i j = 0) :
    normalizedSchur M P Q R C e e₁ e₂
      (if e * e₂ = 1 then i else i.rev) j = 0 := by
  classical
  unfold normalizedSchur
  split_ifs with h
  · simp [scalarNormalizedSchur, signedSchurAt, Matrix.diagonal_mul,
      Matrix.mul_diagonal, hz]
  · simp [reverseRows, scalarNormalizedSchur, signedSchurAt, Matrix.diagonal_mul,
      Matrix.mul_diagonal, hz]

/-- Negative normalized third sign limits every low-rank rectangle.
The bound is deliberately stated for arbitrary finite source index types,
so deleting an essential row or column requires no reindexing. -/
theorem negative_third_rank_rectangle_bound {n p : ℕ} {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    {ε : ℕ → ℝ} (M : Square n) (rows : α → Fin n) (cols : β → Fin n)
    (hrows : StrictMono rows) (hcols : Function.Injective cols)
    (hε : IsSignature n ε) (hM : NonsingularSignRegular ε M)
    (hpn : p + 3 ≤ n) (hp : p ≤ Fintype.card α)
    (hrank : (M.submatrix rows cols).rank ≤ p)
    (hδ : pivotSignature ε p * ε (p + 1) * ε (p + 2) * ε (p + 3) = -1) :
    (Fintype.card α - p) * (Fintype.card β - p) ≤ 2 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (show p ≤ n by omega)
  obtain ⟨I, Q, hI, hQ, hH, hdim, hcover⟩ :=
    exists_pivot_cover_on_rows M rows cols hrows hM.1 hp hrank
  let P := rows ∘ I
  have hP : StrictMono P := hrows.comp hI
  obtain ⟨R, hR, hdisR, hcompR, _⟩ := exists_increasing_complement P hP.injective
  obtain ⟨C, hC, hdisC, hcompC, _⟩ := exists_increasing_complement Q hQ.injective
  let e := pivotSignature ε p
  let Y := normalizedSchur M P Q R C e (ε (p + 1)) (ε (p + 2))
  have he : e = 1 ∨ e = -1 := pivotSignature_sign hε (by omega)
  have he₁ := hε (p + 1) (by omega) (by omega)
  have he₂ := hε (p + 2) (by omega) (by omega)
  have ha : e * ε (p + 1) ≠ 0 := by
    rcases he with hh | hh <;> rcases he₁ with hh₁ | hh₁ <;> simp [hh, hh₁]
  have heH := pivotSignature_mul_det_pos M P Q hP hQ hε hM.2 hH
  have hlower := normalizedSchur_lower_closure M P Q R C hP hQ hR hC hdisR hdisC
    e (ε (p + 1)) (ε (p + 2)) he he₁ he₂ hH heH
    (hM.2.hasSignedMinors (by omega) (by omega))
    (hM.2.hasSignedMinors (by omega) (by omega))
  have hdet : Y.det ≠ 0 := normalizedSchur_nonsingular_complete M P Q R C
    hP.injective hQ.injective hR.injective hC.injective hdisR hdisC
    e (ε (p + 1)) (ε (p + 2)) ha hM.1 hH
  have hthird : NonpositiveThreeMinors Y := by
    have hh := normalizedSchur_third_closure M P Q R C hP hQ hR hC hdisR hdisC
      e (ε (p + 1)) (ε (p + 2)) (ε (p + 3)) he he₁ he₂ hH heH
      (hM.2.hasSignedMinors (by omega) hpn)
    change HasSignedMinors Y 3
      (pivotSignature ε p * ε (p + 1) * ε (p + 2) * ε (p + 3)) at hh
    rw [hδ] at hh
    intro rr cc hrr hcc
    have hh' := hh rr cc hrr hcc
    simpa only [neg_one_mul, neg_nonneg, minor] using hh'
  let α' := {a : α // rows a ∉ Set.range P}
  let β' := {b : β // cols b ∉ Set.range Q}
  have hexR (a : α') : ∃ i, R i = rows a := (hcompR _).mpr a.property
  have hexC (b : β') : ∃ j, C j = cols b := (hcompC _).mpr b.property
  choose f hf using hexR
  choose g hg using hexC
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hrows.injective
    rw [← hf a, ← hf b, hab]
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply hcols
    rw [← hg a, ← hg b, hab]
  let f' : α' → Fin m := fun a => if e * ε (p + 2) = 1 then f a else (f a).rev
  have hf'inj : Function.Injective f' := by
    dsimp [f']
    split_ifs
    · exact hfinj
    · exact Fin.rev_injective.comp hfinj
  have hzero (a : α') (b : β') : Y (f' a) (g b) = 0 := by
    apply normalizedSchur_zero_of_schur_zero
    exact schurAt_entry_zero_of_cover M rows I Q R C a (cols b)
      (f a) (g b) (hf a) (hg b) hH hdim (hcover b)
  have hcount := card_zero_entries_ge_rectangle Y f' g hf'inj hginj hzero
  have hbound := card_zero_entries_le_two hlower.1 hlower.2 hdet hthird
  have hcardR : Fintype.card α - p ≤ Fintype.card α' :=
    card_avoiding_range_ge_sub rows hrows.injective P
  have hcardC : Fintype.card β - p ≤ Fintype.card β' :=
    card_avoiding_range_ge_sub cols hcols Q
  exact (Nat.mul_le_mul hcardR hcardC).trans (hcount.trans hbound)

/-- Section 7.2, negative-third-sign branch: a permanent rank-`p+1`
rectangle of the indicated size cannot contain a free entry. -/
theorem negative_third_free_rectangle_contradiction {n p : ℕ} {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β]
    {ε : ℕ → ℝ} {L U M : Square n}
    (rows : α → Fin n) (cols : β → Fin n)
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (hε : IsSignature n ε) (hminus : NonsingularSignRegular ε (checkerMinus L U))
    (hpn : p + 3 ≤ n) (hcardR : p + 3 ≤ Fintype.card α)
    (hcardC : p + 2 ≤ Fintype.card β)
    (hM : InRelativeInterior L U M)
    (hrank : (M.submatrix rows cols).rank = p + 1)
    (hbound : ∀ X, InBox L U X → (X.submatrix rows cols).rank ≤ p + 1)
    (hlower : ∀ X, InBox L U X → ∀ a b : Fin (p + 1) → Fin n,
      StrictMono a → StrictMono b → 0 ≤ ε (p + 1) * minor X a b)
    (hδ : pivotSignature ε p * ε (p + 1) * ε (p + 2) * ε (p + 3) = -1)
    (i : α) (j : β) (hfree : L (rows i) (cols j) < U (rows i) (cols j)) : False := by
  classical
  have hLU : EntrywiseLE L U := fun a b => (hM.1.1 a b).trans (hM.1.2 a b)
  have hη : ε (p + 1) ≠ 0 := signature_ne_zero hε (by omega) (by omega)
  rcases essential_residual_rank_on_box rows cols hrows hcols hM hrank hbound
      (ε (p + 1)) hη hlower i j hfree with ⟨_, hrow⟩ | ⟨_, hcol⟩
  · have hc : Fintype.card {a : α // a ≠ i} = Fintype.card α - 1 := by simp
    have ha : p ≤ Fintype.card {a : α // a ≠ i} := by rw [hc]; omega
    have hb := negative_third_rank_rectangle_bound (checkerMinus L U)
      (rows ∘ (Subtype.val : {a : α // a ≠ i} → α)) cols
      (hrows.comp (fun _ _ h => h)) hcols.injective hε hminus hpn ha
      (hrow _ (checkerMinus_mem_box hLU)) hδ
    rw [hc] at hb
    have hprod : 4 ≤ (Fintype.card α - 1 - p) * (Fintype.card β - p) :=
      Nat.mul_le_mul (show 2 ≤ Fintype.card α - 1 - p by omega)
        (show 2 ≤ Fintype.card β - p by omega)
    omega
  · have hc : Fintype.card {b : β // b ≠ j} = Fintype.card β - 1 := by simp
    have hb := negative_third_rank_rectangle_bound (checkerMinus L U)
      rows (cols ∘ (Subtype.val : {b : β // b ≠ j} → β)) hrows
      (hcols.injective.comp Subtype.val_injective) hε hminus hpn (by omega)
      (hcol _ (checkerMinus_mem_box hLU)) hδ
    rw [hc] at hb
    have hprod : 3 ≤ (Fintype.card α - p) * (Fintype.card β - 1 - p) :=
      Nat.mul_le_mul (show 3 ≤ Fintype.card α - p by omega)
        (show 1 ≤ Fintype.card β - 1 - p by omega)
    omega

end IV01
