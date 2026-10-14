import IV01.Box

set_option backward.isDefEq.respectTransparency false

namespace IV01

theorem minor_transpose {n k : ℕ} (M : Square n) (rows cols : Fin k → Fin n) :
    minor M.transpose rows cols = minor M cols rows := by
  simp only [minor, ← Matrix.transpose_submatrix, Matrix.det_transpose]

theorem SignRegular.transpose {n : ℕ} {ε : ℕ → ℝ} {M : Square n}
    (hM : SignRegular ε M) : SignRegular ε M.transpose := by
  intro k hk hkn rows cols hr hc
  rw [minor_transpose]
  exact hM k hk hkn cols rows hc hr

theorem NonsingularSignRegular.transpose {n : ℕ} {ε : ℕ → ℝ} {M : Square n}
    (hM : NonsingularSignRegular ε M) : NonsingularSignRegular ε M.transpose :=
  ⟨by simpa only [Matrix.det_transpose] using hM.1, hM.2.transpose⟩

theorem checkerMinus_transpose {n : ℕ} (L U : Square n) :
    checkerMinus L.transpose U.transpose = (checkerMinus L U).transpose := by
  ext i j
  simp [checkerMinus, Matrix.transpose_apply, Nat.add_comm]

theorem checkerPlus_transpose {n : ℕ} (L U : Square n) :
    checkerPlus L.transpose U.transpose = (checkerPlus L U).transpose := by
  ext i j
  simp [checkerPlus, Matrix.transpose_apply, Nat.add_comm]

theorem EntrywiseLE.transpose {n : ℕ} {L U : Square n} (hLU : EntrywiseLE L U) :
    EntrywiseLE L.transpose U.transpose := fun i j => hLU j i

theorem InBox.transpose {n : ℕ} {L U M : Square n} (hM : InBox L U M) :
    InBox L.transpose U.transpose M.transpose := ⟨hM.1.transpose, hM.2.transpose⟩

theorem InRelativeInterior.transpose {n : ℕ} {L U M : Square n}
    (hM : InRelativeInterior L U M) : InRelativeInterior L.transpose U.transpose M.transpose :=
  ⟨hM.1.transpose, fun i j => hM.2 j i⟩

end IV01
