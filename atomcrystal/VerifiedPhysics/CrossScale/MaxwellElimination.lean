import VerifiedPhysics.Atomistic.MaxwellSlab

namespace VerifiedPhysics.MaxwellSlab

theorem reconstruct_ionic_mode (b s : ℝ) (v m : ℕ → ℝ)
    (hd : b-s ≠ 0) (he : eps b s ≠ 0) (hi : epsInterface b s ≠ 0)
    (hm : MagneticMode b s v m) : MaxwellIonMode b s (reconstruct b s v m) := by
  obtain ⟨hn, hv0, hm0, hinterior, hv15, hm15⟩ := hm
  have ionic (w : ℝ) : w / eps b s + 3 * ((w / eps b s) / (b-s)) = w := by
    calc
      _ = eps b s * (w / eps b s) := by unfold eps; ring
      _ = w := mul_div_cancel₀ _ he
  have halfIonic (w : ℝ) : w / epsInterface b s + (3/2 : ℝ) *
      ((w / epsInterface b s) / (b-s)) = w := by
    calc
      _ = epsInterface b s * (w / epsInterface b s) := by unfold epsInterface; ring
      _ = w := mul_div_cancel₀ _ hi
  refine ⟨hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    dsimp [reconstruct]
    exact ⟨ionic _, by field_simp [hd]⟩
  · intro j _
    dsimp [reconstruct]
    exact ⟨rfl, ionic _, by field_simp [hd]⟩
  · exact halfIonic _
  · dsimp [reconstruct]
    field_simp [hd]
  · dsimp [reconstruct]
    linarith
  · dsimp [reconstruct]
    have heq : -8 * (8 * (m (0+1) - m 0) / eps b s) +
        6 * (m 0 / eps b s) - s * m 0 =
        ((70 - eps b s * s) * m 0 - 64 * m 1) / eps b s := by
      field_simp [he]
      ring
    rw [hm0, zero_div] at heq
    linarith
  · intro j hj
    obtain ⟨hv, hm⟩ := hinterior j hj
    constructor
    · dsimp [reconstruct]
      rw [show j+1+1=j+2 by omega]
      linarith
    · dsimp [reconstruct]
      have heq : 8 * (8 * (m (j+1) - m j) / eps b s -
            8 * (m (j+1+1) - m (j+1)) / eps b s) +
          6 * (m (j+1) / eps b s) - s * m (j+1) =
          ((134 - eps b s * s) * m (j+1) - 64 * m j - 64 * m (j+2)) / eps b s := by
        rw [show j+1+1=j+2 by omega]
        field_simp [he]
        ring
      rw [hm, zero_div] at heq
      linarith
  · dsimp [reconstruct]
    unfold interfaceCoupling at hv15
    have heq : 8 * (8 * (v (14+1) - v 14) + 8 * (v 15 - m 15) / epsInterface b s) +
        6 * v 15 - s * v 15 =
        (70 - s + 64 / epsInterface b s) * v 15 - 64 * v 14 -
          (64 / epsInterface b s) * m 15 := by ring
    rw [hv15] at heq
    linarith
  · dsimp [reconstruct]
    have heq : 8 * (8 * (m (14+1) - m 14) / eps b s -
          8 * (v 15 - m 15) / epsInterface b s) + 6 * (m 15 / eps b s) - s * m 15 =
        ((70 - eps b s * s + eps b s * interfaceCoupling b s) * m 15 - 64 * m 14 -
          eps b s * interfaceCoupling b s * v 15) / eps b s := by
      unfold interfaceCoupling
      field_simp [he, hi]
      ring
    rw [hm15, zero_div] at heq
    linarith

end VerifiedPhysics.MaxwellSlab
