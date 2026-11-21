import Grain.ShellPredictionData

/-! The four-spectrum experiment certifies the error of the composed
approximations by checking their lifts in the primitive Hamiltonian. -/

namespace Grain.TwoShell.Prediction

def innerRadius (far : Bool) : ℚ := if far then 5 else 2
def outerRadius (far : Bool) : ℚ := if far then 14 else 6

def prediction (innerFar outerFar : Bool) : Fin 3 → ℚ × ShellWitness :=
  match innerFar, outerFar with
  | false, false => ![(r2s6n6Center, r2s6n6), (r2s6n7Center, r2s6n7), (r2s6n8Center, r2s6n8)]
  | false, true => ![(r2s14n6Center, r2s14n6), (r2s14n7Center, r2s14n7), (r2s14n8Center, r2s14n8)]
  | true, false => ![(r5s6n6Center, r5s6n6), (r5s6n7Center, r5s6n7), (r5s6n8Center, r5s6n8)]
  | true, true => ![(r5s14n6Center, r5s14n6), (r5s14n7Center, r5s14n7), (r5s14n8Center, r5s14n8)]

def witness (r s : Bool) (k : Fin 3) := (prediction r s k).2
def center (r s : Bool) (k : Fin 3) := (prediction r s k).1

set_option maxHeartbeats 1000000 in
private theorem table_rows (r s : Bool) (k : Fin 3) :
    ∀ c, checkRange (innerRadius r) (outerRadius s) (6 + k.val) (witness r s k) c := by
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

private theorem reference_active (k : Fin 3) :
    ∃ a : Occupation, electronCount a = 6 + k.val ∧ active (6 + k.val) a := by
  refine ⟨decode (26 + 27 * k.val), ?_⟩
  fin_cases k <;> decide +kernel

noncomputable def energy (r s : Bool) (k : Fin 3) : ℝ :=
  ground (ratH (innerRadius r) (outerRadius s) (6 + k.val))

theorem sector_bounds (r s : Bool) (k : Fin 3) :
    ((witness r s k).lo : ℝ) ≤ energy r s k ∧
      energy r s k ≤ ((witness r s k).hi : ℝ) :=
  witness_bounds _ _ _ _ (table_rows r s k) (reference_active k)

def sectorTolerance : ℚ := 1 / 10^12

private theorem budget (r s : Bool) (k : Fin 3) :
    center r s k - sectorTolerance ≤ (witness r s k).lo ∧
      (witness r s k).hi ≤ center r s k + sectorTolerance := by
  cases r <;> cases s <;> fin_cases k <;> decide +kernel

/-- Uniform end-to-end error for the two successive approximations on the
twelve sector calculations in the four chosen spectra. -/
theorem sector_error (r s : Bool) (k : Fin 3) :
    |energy r s k - (center r s k : ℝ)| ≤ (sectorTolerance : ℝ) := by
  obtain ⟨hl, hu⟩ := sector_bounds r s k
  have h₁ : ((center r s k - sectorTolerance : ℚ) : ℝ) ≤ ((witness r s k).lo : ℝ) := by
    exact_mod_cast (budget r s k).1
  have h₂ : ((witness r s k).hi : ℝ) ≤ ((center r s k + sectorTolerance : ℚ) : ℝ) := by
    exact_mod_cast (budget r s k).2
  push_cast at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

noncomputable def parityEnergy (r s : Bool) : ℝ :=
  energy r s 1 - (energy r s 0 + energy r s 2) / 2

def parityLo (r s : Bool) : ℚ :=
  (witness r s 1).lo - ((witness r s 0).hi + (witness r s 2).hi) / 2
def parityHi (r s : Bool) : ℚ :=
  (witness r s 1).hi - ((witness r s 0).lo + (witness r s 2).lo) / 2

private theorem parity_bounds (r s : Bool) :
    (parityLo r s : ℝ) ≤ parityEnergy r s ∧ parityEnergy r s ≤ (parityHi r s : ℝ) := by
  obtain ⟨l₀, u₀⟩ := sector_bounds r s 0
  obtain ⟨l₁, u₁⟩ := sector_bounds r s 1
  obtain ⟨l₂, u₂⟩ := sector_bounds r s 2
  simp only [parityEnergy, parityLo, parityHi, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith

noncomputable def mixedContrast : ℝ :=
  parityEnergy false false - parityEnergy false true -
    parityEnergy true false + parityEnergy true true

def mixedLo : ℚ := parityLo false false - parityHi false true - parityHi true false + parityLo true true
def mixedHi : ℚ := parityHi false false - parityLo false true - parityLo true false + parityHi true true

def parityCenter (r s : Bool) : ℚ := center r s 1 - (center r s 0 + center r s 2) / 2
def mixedCenter : ℚ :=
  parityCenter false false - parityCenter false true - parityCenter true false + parityCenter true true

theorem mixed_endpoints :
    mixedLo = 2964650171 / 10^17 ∧
    mixedCenter = 2964666163 / 10^17 ∧
    mixedHi = 2964680015 / 10^17 := by decide +kernel

theorem mixed_bounds : (mixedLo : ℝ) ≤ mixedContrast ∧ mixedContrast ≤ (mixedHi : ℝ) := by
  obtain ⟨la, ua⟩ := parity_bounds false false
  obtain ⟨lb, ub⟩ := parity_bounds false true
  obtain ⟨lc, uc⟩ := parity_bounds true false
  obtain ⟨ld, ud⟩ := parity_bounds true true
  simp only [mixedContrast, mixedLo, mixedHi, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

/-- At fixed bare coupling, the nested reduced model predicts a positive
mixed contrast with a certified absolute error at most 2e-13 in spacing units. -/
theorem verified_two_shell_approximation :
    0 < mixedContrast ∧ |mixedContrast - (mixedCenter : ℝ)| ≤ 2 / 10^13 := by
  obtain ⟨hl, hu⟩ := mixed_bounds
  have h₁ : (0 : ℚ) < mixedLo := by decide +kernel
  have h₂ : mixedCenter - 2 / 10^13 ≤ mixedLo := by decide +kernel
  have h₃ : mixedHi ≤ mixedCenter + 2 / 10^13 := by decide +kernel
  have h₁' : (0 : ℝ) < (mixedLo : ℝ) := by exact_mod_cast h₁
  have h₂' : ((mixedCenter - 2 / 10^13 : ℚ) : ℝ) ≤ (mixedLo : ℝ) := by exact_mod_cast h₂
  have h₃' : (mixedHi : ℝ) ≤ ((mixedCenter + 2 / 10^13 : ℚ) : ℝ) := by exact_mod_cast h₃
  push_cast at h₂' h₃'
  refine ⟨h₁'.trans_le hl, abs_le.mpr ⟨?_, ?_⟩⟩ <;> linarith

end Grain.TwoShell.Prediction
