import Grain.Effective

/-! Frozen prediction. This import closure contains the occupation model and
the arrowhead reduction. All inequalities here are checked using the
free-reference denominators and the row bound for the omitted interactions. -/

namespace Grain

private def validSector (s : Spec) (n : ℕ) : Prop :=
  (∀ i : Basis n, 0 ≤ action (lowerDifference s n) (fun _ => 1) i) ∧
  (∀ i, 0 < lowerWeight s n i) ∧
  (∀ i, sectorLo s n * lowerWeight s n i ≤ action (arrowhead s n (-6)) (lowerWeight s n) i) ∧
  0 < rationalNormSq (upperTrial s n) ∧
  rayleighNumerator (arrowhead s n 6) (upperTrial s n) ≤
    sectorHi s n * rationalNormSq (upperTrial s n)

private instance (s : Spec) (n : ℕ) : Decidable (validSector s n) := by
  unfold validSector
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem verifiedSectors (s : Spec) :
    validSector s 4 ∧ validSector s 5 ∧ validSector s 6 := by
  cases s <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

private theorem sectorPrediction (s : Spec) (n : ℕ) (h : validSector s n) :
    (sectorLo s n : ℝ) ≤ sectorEnergy (spectrum s) n ∧
      sectorEnergy (spectrum s) n ≤ (sectorHi s n : ℝ) := by
  rcases h with ⟨hg, hw, hl, ht, hu⟩
  exact effective_bounds s n hg hw hl ht hu

theorem parity_prediction (s : Spec) :
    (parityCenter s : ℝ) - 2 * (sectorRadius : ℝ) ≤ parity (spectrum s) ∧
    parity (spectrum s) ≤ (parityCenter s : ℝ) + 2 * (sectorRadius : ℝ) := by
  obtain ⟨h4, h5, h6⟩ := verifiedSectors s
  obtain ⟨l4, u4⟩ := sectorPrediction s 4 h4
  obtain ⟨l5, u5⟩ := sectorPrediction s 5 h5
  obtain ⟨l6, u6⟩ := sectorPrediction s 6 h6
  simp only [sectorLo, sectorHi, Rat.cast_sub, Rat.cast_add] at l4 u4 l5 u5 l6 u6
  simp only [parityCenter, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, parity]
  constructor <;> linarith

/-- Moving the outer pair of levels changes just the outer pair-hop denominators
that survive the even–odd subtraction. -/
def shellParityCenter (radius : ℚ) : ℚ := 1 / 2 + (1 / 1000 + 1 / radius) / 2

theorem shellParityCenter_decreases {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    shellParityCenter b < shellParityCenter a := by
  unfold shellParityCenter
  linarith [one_div_lt_one_div_of_lt ha hab]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem shell_center_agrees (s : Spec) :
    parityCenter s = shellParityCenter (s.radius : ℚ) := by
  cases s <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem contrast_center : parityCenter .near - parityCenter .far = contrastCenter := by
  decide +kernel

theorem prediction_window :
    (predictedLo : ℝ) ≤ parity (spectrum .near) - parity (spectrum .far) ∧
    parity (spectrum .near) - parity (spectrum .far) ≤ (predictedHi : ℝ) := by
  have hc : (parityCenter .near : ℝ) - (parityCenter .far : ℝ) = (contrastCenter : ℝ) := by
    exact_mod_cast contrast_center
  obtain ⟨ln, un⟩ := parity_prediction .near
  obtain ⟨lf, uf⟩ := parity_prediction .far
  simp only [predictedLo, predictedHi, Rat.cast_sub, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  constructor <;> linarith

theorem frozen_endpoints :
    predictedLo = 4 / 56250 ∧ predictedHi = 17 / 112500 := by decide +kernel

theorem prediction_positive : 0 < predictedLo := by decide +kernel

end Grain
