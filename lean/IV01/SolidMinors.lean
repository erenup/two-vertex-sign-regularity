import IV01.CheckerMonotone

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem exists_box_extension {n k : ℕ} {L U : Square n}
    (hLU : EntrywiseLE L U) (rows cols : Fin k → Fin n)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (Y : Square k) (hY : InBox (L.submatrix rows cols) (U.submatrix rows cols) Y) :
    ∃ X : Square n, InBox L U X ∧ X.submatrix rows cols = Y := by
  classical
  let e : Fin k × Fin k → Fin n × Fin n := fun ij => (rows ij.1, cols ij.2)
  have he : Function.Injective e := by
    intro a b hab
    exact Prod.ext (hr (congrArg Prod.fst hab)) (hc (congrArg Prod.snd hab))
  let f := Function.extend e (Function.uncurry Y) (Function.uncurry L)
  let X : Square n := Function.curry f
  have hsub : X.submatrix rows cols = Y := by
    ext i j
    exact he.extend_apply _ _ (i, j)
  refine ⟨X, ?_, hsub⟩
  constructor <;> intro i j
  · by_cases h : ∃ ij, e ij = (i, j)
    · obtain ⟨⟨a, b⟩, hab⟩ := h
      have ha : rows a = i := congrArg Prod.fst hab
      have hb : cols b = j := congrArg Prod.snd hab
      rw [← ha, ← hb]
      change L (rows a) (cols b) ≤ X.submatrix rows cols a b
      rw [hsub]
      exact hY.1 a b
    · change L i j ≤ Function.extend e (Function.uncurry Y) (Function.uncurry L) (i, j)
      rw [Function.extend_apply' _ _ _ h]
      exact le_rfl
  · by_cases h : ∃ ij, e ij = (i, j)
    · obtain ⟨⟨a, b⟩, hab⟩ := h
      have ha : rows a = i := congrArg Prod.fst hab
      have hb : cols b = j := congrArg Prod.snd hab
      rw [← ha, ← hb]
      change X.submatrix rows cols a b ≤ U (rows a) (cols b)
      rw [hsub]
      exact hY.2 a b
    · change Function.extend e (Function.uncurry Y) (Function.uncurry L) (i, j) ≤ U i j
      rw [Function.extend_apply' _ _ _ h]
      exact hLU i j

def consecutiveIndices (n k a : ℕ) (ha : a + k ≤ n) : Fin k → Fin n :=
  fun i => ⟨a + i.val, by have := i.isLt; omega⟩

theorem consecutiveIndices_strictMono {n k a : ℕ} (ha : a + k ≤ n) :
    StrictMono (consecutiveIndices n k a ha) := by
  intro i j hij
  exact Nat.add_lt_add_left hij a

theorem checker_submatrix_consecutive {n k a b : ℕ} (L U : Square n)
    (ha : a + k ≤ n) (hb : b + k ≤ n) :
    let rows := consecutiveIndices n k a ha
    let cols := consecutiveIndices n k b hb
    ((checkerMinus L U).submatrix rows cols =
      checkerMinus (L.submatrix rows cols) (U.submatrix rows cols) ∧
     (checkerPlus L U).submatrix rows cols =
      checkerPlus (L.submatrix rows cols) (U.submatrix rows cols)) ∨
    ((checkerMinus L U).submatrix rows cols =
      checkerPlus (L.submatrix rows cols) (U.submatrix rows cols) ∧
     (checkerPlus L U).submatrix rows cols =
      checkerMinus (L.submatrix rows cols) (U.submatrix rows cols)) := by
  dsimp only
  by_cases hab : (a + b) % 2 = 0
  · left
    constructor <;> ext i j <;>
      simp only [Matrix.submatrix_apply, checkerMinus, checkerPlus, consecutiveIndices]
    all_goals
      have h : (a + i.val + (b + j.val)) % 2 = 0 ↔ (i.val + j.val) % 2 = 0 := by omega
      simp only [h]
  · right
    constructor <;> ext i j <;>
      simp only [Matrix.submatrix_apply, checkerMinus, checkerPlus, consecutiveIndices]
    all_goals
      have h : (a + i.val + (b + j.val)) % 2 = 0 ↔ ¬(i.val + j.val) % 2 = 0 := by omega
      simp only [h]
      split_ifs <;> rfl

/-- Once all minors of order k-1 have the prescribed sign on the box,
every solid k-minor has its prescribed sign. Here k=q+2, so order one
is the first required cofactor order. -/
theorem solid_minor_sign {n q a b : ℕ} {ε : ℕ → ℝ} {L U M : Square n}
    (hLU : EntrywiseLE L U) (hε : IsSignature n ε)
    (hminus : SignRegular ε (checkerMinus L U))
    (hplus : SignRegular ε (checkerPlus L U))
    (ha : a + (q + 2) ≤ n) (hb : b + (q + 2) ≤ n)
    (hlower : ∀ X, InBox L U X → ∀ r c : Fin (q + 1) → Fin n,
      StrictMono r → StrictMono c → 0 ≤ ε (q + 1) * minor X r c)
    (hM : InBox L U M) :
    0 ≤ ε (q + 2) * minor M
      (consecutiveIndices n (q + 2) a ha) (consecutiveIndices n (q + 2) b hb) := by
  let rows := consecutiveIndices n (q + 2) a ha
  let cols := consecutiveIndices n (q + 2) b hb
  have hr : StrictMono rows := consecutiveIndices_strictMono ha
  have hc : StrictMono cols := consecutiveIndices_strictMono hb
  have hLU' : EntrywiseLE (L.submatrix rows cols) (U.submatrix rows cols) :=
    fun i j => hLU (rows i) (cols j)
  have hcf : ∀ Y, InBox (L.submatrix rows cols) (U.submatrix rows cols) Y →
      ∀ i j : Fin (q + 2),
      0 ≤ ε (q + 1) * (Y.submatrix i.succAbove j.succAbove).det := by
    intro Y hY i j
    obtain ⟨X, hX, hsub⟩ := exists_box_extension hLU rows cols hr.injective hc.injective Y hY
    rw [← hsub, Matrix.submatrix_submatrix]
    exact hlower X hX (rows ∘ i.succAbove) (cols ∘ j.succAbove)
      (hr.comp (Fin.strictMono_succAbove i)) (hc.comp (Fin.strictMono_succAbove j))
  have hma : 0 ≤ ε (q + 2) * ((checkerMinus L U).submatrix rows cols).det :=
    hminus (q + 2) (by omega) (by omega) rows cols hr hc
  have hmb : 0 ≤ ε (q + 2) * ((checkerPlus L U).submatrix rows cols).det :=
    hplus (q + 2) (by omega) (by omega) rows cols hr hc
  have hends := checker_submatrix_consecutive L U ha hb
  change
    ((checkerMinus L U).submatrix rows cols =
      checkerMinus (L.submatrix rows cols) (U.submatrix rows cols) ∧
     (checkerPlus L U).submatrix rows cols =
      checkerPlus (L.submatrix rows cols) (U.submatrix rows cols)) ∨
    ((checkerMinus L U).submatrix rows cols =
      checkerPlus (L.submatrix rows cols) (U.submatrix rows cols) ∧
     (checkerPlus L U).submatrix rows cols =
      checkerMinus (L.submatrix rows cols) (U.submatrix rows cols)) at hends
  change 0 ≤ ε (q + 2) * (M.submatrix rows cols).det
  apply determinant_sign_of_checker_endpoints hLU' (ε (q + 1)) (ε (q + 2))
    (hε (q + 1) (by omega) (by omega)) hcf
  · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₁] using hma
    · simpa only [h₂] using hmb
  · rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · simpa only [h₂] using hmb
    · simpa only [h₁] using hma
  · exact ⟨fun i j => hM.1 (rows i) (cols j), fun i j => hM.2 (rows i) (cols j)⟩

end IV01
