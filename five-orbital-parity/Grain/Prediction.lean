import Grain.Effective

/-! Five-orbital prediction from the spectrum and the pair-transfer rules.
The sector bounds use a discarded-pivot positivity check for the chosen spectra. -/

namespace Grain

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem discarded_pivot_pos (s : Spec) (c : Fin 3) :
    ∀ i ∈ RankOne.tail (referenceIndex c),
      0 < tailDiagonal (spectrum s) c i - tailAllowance c - referenceEnergy (spectrum s) c := by
  cases s <;> fin_cases c <;> decide +kernel

theorem sector_prediction (s : Spec) (c : Fin 3) :
    (sectorLo (spectrum s) c : ℝ) ≤ sectorEnergy (spectrum s) (4 + c.val) ∧
      sectorEnergy (spectrum s) (4 + c.val) ≤ (sectorHi (spectrum s) c : ℝ) :=
  effective_bounds (spectrum s) c (discarded_pivot_pos s c)

def bareParity (levels : Fin 5 → ℤ) : ℚ :=
  referenceEnergy levels 1 - (referenceEnergy levels 0 + referenceEnergy levels 2) / 2

def parityLo (levels : Fin 5 → ℤ) : ℚ :=
  sectorLo levels 1 - (sectorHi levels 0 + sectorHi levels 2) / 2

def parityHi (levels : Fin 5 → ℤ) : ℚ :=
  sectorHi levels 1 - (sectorLo levels 0 + sectorLo levels 2) / 2

theorem parity_prediction (s : Spec) :
    (parityLo (spectrum s) : ℝ) ≤ parity (spectrum s) ∧
      parity (spectrum s) ≤ (parityHi (spectrum s) : ℝ) := by
  have h4 : _ ≤ sectorEnergy (spectrum s) 4 ∧ sectorEnergy (spectrum s) 4 ≤ _ :=
    sector_prediction s 0
  have h5 : _ ≤ sectorEnergy (spectrum s) 5 ∧ sectorEnergy (spectrum s) 5 ≤ _ :=
    sector_prediction s 1
  have h6 : _ ≤ sectorEnergy (spectrum s) 6 ∧ sectorEnergy (spectrum s) 6 ≤ _ :=
    sector_prediction s 2
  obtain ⟨l4, u4⟩ := h4
  obtain ⟨l5, u5⟩ := h5
  obtain ⟨l6, u6⟩ := h6
  simp only [parity, parityLo, parityHi, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith

def predictedLo : ℚ := parityLo (spectrum .near) - parityHi (spectrum .far)
def predictedHi : ℚ := parityHi (spectrum .near) - parityLo (spectrum .far)

theorem prediction_window :
    (predictedLo : ℝ) ≤ parity (spectrum .near) - parity (spectrum .far) ∧
    parity (spectrum .near) - parity (spectrum .far) ≤ (predictedHi : ℝ) := by
  obtain ⟨ln, un⟩ := parity_prediction .near
  obtain ⟨lf, uf⟩ := parity_prediction .far
  simp only [predictedLo, predictedHi, Rat.cast_sub]
  constructor <;> linarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem prediction_decimal_enclosure :
    (10623598 / 10^11 : ℚ) ≤ predictedLo ∧ predictedHi ≤ 11598659 / 10^11 := by
  decide +kernel

theorem prediction_positive : 0 < predictedLo :=
  lt_of_lt_of_le (by norm_num) prediction_decimal_enclosure.1

end Grain
