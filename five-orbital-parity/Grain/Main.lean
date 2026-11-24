import Grain.Prediction
import Grain.Certificate

namespace Grain

open Certificate

theorem near_input : nearSpectrum = spectrum .near := by
  funext i
  fin_cases i <;> decide +kernel

theorem far_input : farSpectrum = spectrum .far := by
  funext i
  fin_cases i <;> decide +kernel

def observedLo : ℚ :=
  near5.lo - (near4.hi + near6.hi) / 2 - (far5.hi - (far4.lo + far6.lo) / 2)

def observedHi : ℚ :=
  near5.hi - (near4.lo + near6.lo) / 2 - (far5.lo - (far4.hi + far6.hi) / 2)

theorem full_model_window :
    (observedLo : ℝ) ≤ parity (spectrum .near) - parity (spectrum .far) ∧
    parity (spectrum .near) - parity (spectrum .far) ≤ (observedHi : ℝ) := by
  obtain ⟨ln4, un4⟩ := near4.bounds _ near4_valid
  obtain ⟨ln5, un5⟩ := near5.bounds _ near5_valid
  obtain ⟨ln6, un6⟩ := near6.bounds _ near6_valid
  obtain ⟨lf4, uf4⟩ := far4.bounds _ far4_valid
  obtain ⟨lf5, uf5⟩ := far5.bounds _ far5_valid
  obtain ⟨lf6, uf6⟩ := far6.bounds _ far6_valid
  simp only [near_input, far_input] at *
  simp only [parity, observedLo, observedHi, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith

theorem observed_endpoints :
    observedLo = 11129 / 100000000 ∧ observedHi = 11141 / 100000000 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem agreement : predictedLo ≤ observedLo ∧ observedHi ≤ predictedHi := by
  decide +kernel

/-- Both bare reference parity energies come directly from the Hamiltonian. -/
theorem reference_control :
    bareParity (spectrum .near) - bareParity (spectrum .far) = 0 := by
  decide +kernel

/-- The independently certified reduced-BCS contrast falls within the positive
window derived by eliminating the discarded configurations. -/
theorem verified_five_orbital_eft :
    bareParity (spectrum .near) - bareParity (spectrum .far) = 0 ∧
    (0 : ℝ) < predictedLo ∧
    (predictedLo : ℝ) ≤ observedLo ∧
    (observedLo : ℝ) ≤ parity (spectrum .near) - parity (spectrum .far) ∧
    parity (spectrum .near) - parity (spectrum .far) ≤ (observedHi : ℝ) ∧
    (observedHi : ℝ) ≤ predictedHi := by
  refine ⟨reference_control, ?_, ?_, full_model_window.1, full_model_window.2, ?_⟩
  · exact_mod_cast prediction_positive
  · exact_mod_cast agreement.1
  · exact_mod_cast agreement.2

/-- The same enclosure with the arbitrary-offset central-orbital control. -/
theorem verified_shell_dependent_pairing (nearOuter farOuter offset : ℚ) :
    frozenBareParity nearOuter offset - frozenBareParity farOuter offset = 0 ∧
    (0 : ℝ) < predictedLo ∧
    (predictedLo : ℝ) ≤ observedLo ∧
    (observedLo : ℝ) ≤ parity (spectrum .near) - parity (spectrum .far) ∧
    parity (spectrum .near) - parity (spectrum .far) ≤ (observedHi : ℝ) ∧
    (observedHi : ℝ) ≤ predictedHi :=
  ⟨by simp [frozenBareParity_eq], verified_five_orbital_eft.2⟩

end Grain
