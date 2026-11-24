import Grain.Model

namespace Grain

structure Witness (n : ℕ) where
  lo : ℚ
  hi : ℚ
  lower : Basis n → ℚ
  trial : Basis n → ℚ

def Witness.Valid {n : ℕ} (w : Witness n) (s : Fin 5 → ℤ) : Prop :=
  (∀ i, 0 < w.lower i) ∧
  (∀ i, w.lo * w.lower i ≤ action (hamiltonian s n) w.lower i) ∧
  0 < rationalNormSq w.trial ∧
  rayleighNumerator (hamiltonian s n) w.trial ≤ w.hi * rationalNormSq w.trial

instance {n : ℕ} (w : Witness n) (s : Fin 5 → ℤ) : Decidable (w.Valid s) := by
  unfold Witness.Valid
  infer_instance

theorem Witness.bounds {n : ℕ} (w : Witness n) (s : Fin 5 → ℤ) (h : w.Valid s) :
    (w.lo : ℝ) ≤ sectorEnergy s n ∧ sectorEnergy s n ≤ (w.hi : ℝ) := by
  rcases h with ⟨hw, hl, ht, hu⟩
  exact ground_bounds _ _ _
    (weighted_lower _ _ _ (hamiltonian_symm s n) (hamiltonian_nonpos s n) hw hl)
    (normalized_trial _ _ ht _ hu)

end Grain
