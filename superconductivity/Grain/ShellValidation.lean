import Grain.ShellFullData
import Grain.ShellPrediction

/-! Compare the full occupation solve with the frozen nested reduction. -/

namespace Grain.TwoShell.FullSolve

def witness (innerFar outerFar : Bool) : Fin 3 → ShellWitness :=
  match innerFar, outerFar with
  | false, false => ![r2s6n6, r2s6n7, r2s6n8]
  | false, true => ![r2s14n6, r2s14n7, r2s14n8]
  | true, false => ![r5s6n6, r5s6n7, r5s6n8]
  | true, true => ![r5s14n6, r5s14n7, r5s14n8]

set_option maxHeartbeats 1000000 in
theorem witness_rows (r s : Bool) (k : Fin 3) :
    ∀ c, checkRange (Prediction.innerRadius r) (Prediction.outerRadius s)
      (6 + k.val) (witness r s k) c := by
  cases r <;> cases s <;> fin_cases k
  · exact r2s6n6Rows
  · exact r2s6n7Rows
  · exact r2s6n8Rows
  · exact r2s14n6Rows
  · exact r2s14n7Rows
  · exact r2s14n8Rows
  · exact r5s6n6Rows
  · exact r5s6n7Rows
  · exact r5s6n8Rows
  · exact r5s14n6Rows
  · exact r5s14n7Rows
  · exact r5s14n8Rows

theorem sector_bounds (r s : Bool) (k : Fin 3) :
    ((witness r s k).lo : ℝ) ≤ Prediction.energy r s k ∧
      Prediction.energy r s k ≤ ((witness r s k).hi : ℝ) := by
  apply witness_bounds _ _ _ _ (witness_rows r s k)
  refine ⟨decode (26 + 27 * k.val), ?_⟩
  fin_cases k <;> decide +kernel

def parityLo (r s : Bool) : ℚ :=
  (witness r s 1).lo - ((witness r s 0).hi + (witness r s 2).hi) / 2

def parityHi (r s : Bool) : ℚ :=
  (witness r s 1).hi - ((witness r s 0).lo + (witness r s 2).lo) / 2

private theorem parity_bounds (r s : Bool) :
    (parityLo r s : ℝ) ≤ Prediction.parityEnergy r s ∧
    Prediction.parityEnergy r s ≤ (parityHi r s : ℝ) := by
  obtain ⟨l₀, u₀⟩ := sector_bounds r s 0
  obtain ⟨l₁, u₁⟩ := sector_bounds r s 1
  obtain ⟨l₂, u₂⟩ := sector_bounds r s 2
  simp only [Prediction.parityEnergy, parityLo, parityHi,
    Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith

def mixedLo : ℚ := parityLo false false - parityHi false true - parityHi true false + parityLo true true
def mixedHi : ℚ := parityHi false false - parityLo false true - parityLo true false + parityHi true true

theorem mixed_bounds :
    (mixedLo : ℝ) ≤ Prediction.mixedContrast ∧ Prediction.mixedContrast ≤ (mixedHi : ℝ) := by
  obtain ⟨la, ua⟩ := parity_bounds false false
  obtain ⟨lb, ub⟩ := parity_bounds false true
  obtain ⟨lc, uc⟩ := parity_bounds true false
  obtain ⟨ld, ud⟩ := parity_bounds true true
  simp only [Prediction.mixedContrast, mixedLo, mixedHi, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem full_endpoints :
    mixedLo = 29646661616 / 10^18 ∧ mixedHi = 29646661624 / 10^18 := by
  decide +kernel

/-- The contrast from the primitive occupation Hamiltonians lies in the
frozen prediction window. Only the full-solve rows bound the sector energies
in this comparison. -/
theorem full_solve_matches_frozen_prediction :
    (Prediction.mixedLo : ℝ) ≤ (mixedLo : ℝ) ∧
    (mixedLo : ℝ) ≤ Prediction.mixedContrast ∧
    Prediction.mixedContrast ≤ (mixedHi : ℝ) ∧
    (mixedHi : ℝ) ≤ (Prediction.mixedHi : ℝ) := by
  have hl : Prediction.mixedLo ≤ mixedLo := by decide +kernel
  have hu : mixedHi ≤ Prediction.mixedHi := by decide +kernel
  exact ⟨by exact_mod_cast hl, mixed_bounds.1, mixed_bounds.2, by exact_mod_cast hu⟩

/-- The two-shell prediction center agrees with the full model to the last
reported digits of the frozen center. -/
theorem independent_prediction_error :
    |Prediction.mixedContrast - (Prediction.mixedCenter : ℝ)| ≤ 14 / 10^18 := by
  obtain ⟨hl, hu⟩ := mixed_bounds
  have hlo : Prediction.mixedCenter - 14 / 10^18 ≤ mixedLo := by decide +kernel
  have hhi : mixedHi ≤ Prediction.mixedCenter + 14 / 10^18 := by decide +kernel
  have hlo' : ((Prediction.mixedCenter - 14 / 10^18 : ℚ) : ℝ) ≤ (mixedLo : ℝ) := by
    exact_mod_cast hlo
  have hhi' : (mixedHi : ℝ) ≤ ((Prediction.mixedCenter + 14 / 10^18 : ℚ) : ℝ) := by
    exact_mod_cast hhi
  push_cast at hlo' hhi'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Grain.TwoShell.FullSolve
