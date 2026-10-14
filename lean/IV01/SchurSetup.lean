import IV01.PivotIndices
import IV01.IndexSelection
import IV01.SchurClosure

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem exists_increasing_complement_of_le {n p : ℕ} (hp : p ≤ n)
    (P : Fin p → Fin n) (hP : Function.Injective P) :
    ∃ R : Fin (n - p) → Fin n, StrictMono R ∧
      (∀ i j, P i ≠ R j) ∧ (∀ x, x ∈ Set.range R ↔ x ∉ Set.range P) := by
  generalize hm : n - p = m at *
  have hn : n = p + m := by omega
  subst n
  obtain ⟨R, hR, hd, hc, _⟩ := exists_increasing_complement P hP
  exact (show ∃ R : Fin m → Fin (p + m), StrictMono R ∧
    (∀ i j, P i ≠ R j) ∧ (∀ x, x ∈ Set.range R ↔ x ∉ Set.range P) from
      ⟨R, hR, hd, hc⟩)

theorem normalizedSchur_nonsingular_of_le {n p : ℕ} (hp : p ≤ n) (M : Square n)
    (P Q : Fin p → Fin n) (R C : Fin (n-p) → Fin n)
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hR : Function.Injective R) (hC : Function.Injective C)
    (hdisR : ∀ i j, P i ≠ R j) (hdisC : ∀ i j, Q i ≠ C j)
    (e e₁ e₂ : ℝ) (ha : e * e₁ ≠ 0)
    (hM : M.det ≠ 0) (hH : (M.submatrix P Q).det ≠ 0) :
    (normalizedSchur M P Q R C e e₁ e₂).det ≠ 0 := by
  generalize hm : n - p = m at *
  have hn : n = p + m := by omega
  subst n
  exact normalizedSchur_nonsingular_complete M P Q R C hP hQ hR hC
    hdisR hdisC e e₁ e₂ ha hM hH

/-- The complement of an interior pivot retains the two outer columns. -/
theorem complement_middle_endpoints {p : ℕ}
    (P : Fin p → Fin (p+1)) (C : Fin 3 → Fin (p+3)) (hC : StrictMono C)
    (hcomp : ∀ x, x ∈ Set.range C ↔ x ∉ Set.range (middleIndices ∘ P)) :
    C 0 = 0 ∧ C 2 = Fin.last (p+2) := by
  have h0 : (0 : Fin (p+3)) ∉ Set.range (middleIndices ∘ P) := by
    rintro ⟨i, hi⟩
    have hh := middleIndices_pos (P i)
    change middleIndices (P i) = 0 at hi
    rw [hi] at hh
    exact (lt_irrefl _) hh
  have hl : Fin.last (p+2) ∉ Set.range (middleIndices ∘ P) := by
    rintro ⟨i, hi⟩
    have hh := middleIndices_lt_last (P i)
    change middleIndices (P i) = Fin.last (p+2) at hi
    rw [hi] at hh
    exact (lt_irrefl _) hh
  obtain ⟨a, ha⟩ := (hcomp 0).mpr h0
  obtain ⟨b, hb⟩ := (hcomp (Fin.last (p+2))).mpr hl
  constructor
  · apply le_antisymm
    · rw [← ha]
      exact hC.monotone (Fin.zero_le a)
    · exact Fin.zero_le _
  · apply le_antisymm (Fin.le_last _)
    rw [← hb]
    exact hC.monotone (Fin.le_last b)

/-- All index witnesses needed to transport a target minor through a pivot
chosen in its rows and its interior columns. -/
structure SchurFrame {n p : ℕ} (rows cols : Fin (p+3) → Fin n)
    (rp : Fin p → Fin (p+3)) (cp : Fin p → Fin (p+1)) where
  R : Fin (n-p) → Fin n
  C : Fin (n-p) → Fin n
  hR : StrictMono R
  hC : StrictMono C
  disR : ∀ i j, (rows ∘ rp) i ≠ R j
  disC : ∀ i j, (cols ∘ middleIndices ∘ cp) i ≠ C j
  compR : ∀ x, x ∈ Set.range R ↔ x ∉ Set.range (rows ∘ rp)
  compC : ∀ x, x ∈ Set.range C ↔ x ∉ Set.range (cols ∘ middleIndices ∘ cp)
  r : Fin 3 → Fin (n-p)
  c : Fin 3 → Fin (n-p)
  hr : StrictMono r
  hc : StrictMono c
  rr : Fin 3 → Fin (p+3)
  cc : Fin 3 → Fin (p+3)
  hrr : StrictMono rr
  hcc : StrictMono cc
  rows_eq : R ∘ r = rows ∘ rr
  cols_eq : C ∘ c = cols ∘ cc
  local_compR : ∀ x, x ∈ Set.range rr ↔ x ∉ Set.range rp
  local_compC : ∀ x, x ∈ Set.range cc ↔ x ∉ Set.range (middleIndices ∘ cp)
  col_first : C (c 0) = cols 0
  col_last : C (c 2) = cols (Fin.last (p+2))
  σ : Equiv.Perm (Fin (p+3))
  τ : Equiv.Perm (Fin (p+3))
  sortR : appendIndices (rows ∘ rp) (R ∘ r) = rows ∘ σ
  sortC : appendIndices (cols ∘ middleIndices ∘ cp) (C ∘ c) = cols ∘ τ

theorem exists_schurFrame {n p : ℕ} (hp : p ≤ n)
    (rows cols : Fin (p+3) → Fin n) (hrows : StrictMono rows) (hcols : StrictMono cols)
    (rp : Fin p → Fin (p+3)) (cp : Fin p → Fin (p+1))
    (hrp : StrictMono rp) (hcp : StrictMono cp) : Nonempty (SchurFrame rows cols rp cp) := by
  obtain ⟨R, hR, hdR, hcoR⟩ := exists_increasing_complement_of_le hp
    (rows ∘ rp) (hrows.comp hrp).injective
  obtain ⟨C, hC, hdC, hcoC⟩ := exists_increasing_complement_of_le hp
    (cols ∘ middleIndices ∘ cp) (hcols.comp (strictMono_middleIndices.comp hcp)).injective
  obtain ⟨rr, hrr, hrd, hrc, σ, hσ⟩ := exists_complement_inside rows hrows rp hrp
  obtain ⟨cc, hcc, hcd, hccp, τ, hτ⟩ := exists_complement_inside cols hcols
    (middleIndices ∘ cp) (strictMono_middleIndices.comp hcp)
  obtain ⟨r, hr, her⟩ := exists_strictMono_lift R hR (rows ∘ rr) (hrows.comp hrr) (by
    intro j
    apply (hcoR _).mpr
    rintro ⟨i, hi⟩
    exact hrd i j (hrows.injective hi))
  obtain ⟨c, hc, hec⟩ := exists_strictMono_lift C hC (cols ∘ cc) (hcols.comp hcc) (by
    intro j
    apply (hcoC _).mpr
    rintro ⟨i, hi⟩
    exact hcd i j (hcols.injective hi))
  obtain ⟨hc0, hc2⟩ := complement_middle_endpoints cp cc hcc hccp
  refine ⟨⟨R, C, hR, hC, hdR, hdC, hcoR, hcoC, r, c, hr, hc, rr, cc,
    hrr, hcc, her, hec, hrc, hccp, ?_, ?_, σ, τ, ?_, ?_⟩⟩
  · simpa only [Function.comp_apply, hc0] using congrFun hec 0
  · simpa only [Function.comp_apply, hc2] using congrFun hec 2
  · rw [her]
    exact hσ
  · rw [hec]
    exact hτ

end IV01
