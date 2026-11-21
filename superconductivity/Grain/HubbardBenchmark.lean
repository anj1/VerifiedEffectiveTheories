import Grain.HubbardData
import Grain.CrystalBCSExample
import Grain.HubbardOperators

/-! Applicability of the channel reductions for the fixed four-site
grand-canonical benchmark, measured by its finite-field pair response. -/

namespace Grain.HubbardChannels

theorem crystal_input :
    (∀ a b : Momentum, (hopping (xor a b) : ℚ) / 8 =
      CrystalBCS.normal CrystalBCS.Certificate.crystal a b -
        (if a = b then CrystalBCS.Certificate.crystal.chemicalPotential else 0)) ∧
    (∀ k : Momentum, (levels k : ℚ) / 8 = CrystalBCS.Certificate.levels k) ∧
    (∀ a : Momentum,
      CrystalBCS.attraction CrystalBCS.Certificate.crystal a = 3/2) := by decide +kernel

inductive Temperature
  | cold | warm
  deriving DecidableEq

/-- Temperature in fortieths of a meV. -/
def divisor : Temperature → ℕ
  | .cold => 8
  | .warm => 20

def lower : Temperature → Fin 8 → ℚ
  | .cold => ![m0Response0Lo, m1Response0Lo, m2Response0Lo, m3Response0Lo,
      m4Response0Lo, m5Response0Lo, m6Response0Lo, m7Response0Lo]
  | .warm => ![m0Response1Lo, m1Response1Lo, m2Response1Lo, m3Response1Lo,
      m4Response1Lo, m5Response1Lo, m6Response1Lo, m7Response1Lo]

def upper : Temperature → Fin 8 → ℚ
  | .cold => ![m0Response0Hi, m1Response0Hi, m2Response0Hi, m3Response0Hi,
      m4Response0Hi, m5Response0Hi, m6Response0Hi, m7Response0Hi]
  | .warm => ![m0Response1Hi, m1Response1Hi, m2Response1Hi, m3Response1Hi,
      m4Response1Hi, m5Response1Hi, m6Response1Hi, m7Response1Hi]

noncomputable def response (t : Temperature) (mask : Fin 8) : ℝ :=
  benchmarkResponse mask (divisor t)

theorem benchmark_bounds (t : Temperature) (mask : Fin 8) :
    (lower t mask : ℝ) ≤ response t mask ∧ response t mask ≤ (upper t mask : ℝ) := by
  cases t
  · fin_cases mask
    exacts [m0Response0, m1Response0, m2Response0, m3Response0,
      m4Response0, m5Response0, m6Response0, m7Response0]
  · fin_cases mask
    exacts [m0Response1, m1Response1, m2Response1, m3Response1,
      m4Response1, m5Response1, m6Response1, m7Response1]

/-- One percent relative to the full Hubbard response. -/
def withinBudget (t : Temperature) (mask : Fin 8) : Prop :=
  |response t mask - response t 7| ≤ response t 7 / 100

private def includesDensity (t : Temperature) (mask : Fin 8) : Bool :=
  mask == 7 || (t == .cold && mask.val.testBit 0)

private def accuracyTest (t : Temperature) (mask : Fin 8) : Prop :=
  if includesDensity t mask then
    100 * (upper t mask - lower t 7) ≤ lower t 7 ∧
    100 * (upper t 7 - lower t mask) ≤ lower t 7
  else
    upper t 7 < 100 * (lower t mask - upper t 7)

private instance (t : Temperature) (mask : Fin 8) : Decidable (accuracyTest t mask) := by
  unfold accuracyTest
  infer_instance

theorem budget_characterization (t : Temperature) (mask : Fin 8) :
    withinBudget t mask ↔ includesDensity t mask = true := by
  have hc : accuracyTest t mask := by
    cases t <;> revert mask <;> decide +kernel
  have hm := benchmark_bounds t mask
  have hf := benchmark_bounds t 7
  unfold withinBudget accuracyTest at *
  by_cases h : includesDensity t mask = true
  · rw [if_pos h] at hc
    obtain ⟨h₁, h₂⟩ := hc
    have h₁' : (100 : ℝ) * ((upper t mask : ℝ) - lower t 7) ≤ lower t 7 := by exact_mod_cast h₁
    have h₂' : (100 : ℝ) * ((upper t 7 : ℝ) - lower t mask) ≤ lower t 7 := by exact_mod_cast h₂
    refine ⟨fun _ => h, fun _ => abs_le.mpr ?_⟩
    constructor
    · linarith only [hm.1, hf.1, hf.2, h₂']
    · linarith only [hm.2, hf.1, h₁']
  · rw [if_neg h] at hc
    have hc' : (upper t 7 : ℝ) < (100 : ℝ) * ((lower t mask : ℝ) - upper t 7) := by
      exact_mod_cast hc
    refine iff_of_false (fun he => ?_) h
    linarith [(abs_le.mp he).2, hm.1, hf.2]

inductive Applicability
  | applicable | inapplicable | unassessed
  deriving DecidableEq, Repr

/-- For the benchmark sample, source and chemical potential.
The argument is the temperature in fortieths of a meV. -/
def applicability (mask : Fin 8) (d : ℕ) : Applicability :=
  if d = 8 then
    if includesDensity .cold mask then .applicable else .inapplicable
  else if d = 20 then
    if includesDensity .warm mask then .applicable else .inapplicable
  else .unassessed

theorem applicable_iff (t : Temperature) (mask : Fin 8) :
    applicability mask (divisor t) = .applicable ↔ withinBudget t mask := by
  rw [budget_characterization]
  cases t <;> simp [applicability, divisor] <;> split <;> simp_all

theorem inapplicable_iff (t : Temperature) (mask : Fin 8) :
    applicability mask (divisor t) = .inapplicable ↔ ¬ withinBudget t mask := by
  rw [budget_characterization]
  cases t <;> simp [applicability, divisor] <;> split <;> simp_all

theorem unassessed_iff (mask : Fin 8) (d : ℕ) :
    applicability mask d = .unassessed ↔ d ≠ 8 ∧ d ≠ 20 := by
  unfold applicability
  split <;> split <;> simp_all <;> split <;> simp_all

theorem spin_invariant_reduction :
    withinBudget .cold 3 ∧ ¬ withinBudget .warm 3 :=
  ⟨(applicable_iff .cold 3).mp (by decide), (inapplicable_iff .warm 3).mp (by decide)⟩

def restore (mask : Fin 8) (bit : Fin 3) : Fin 8 := Fin.ofNat 8 (mask.val ||| 2^bit.val)

def marginalThreshold : Temperature → ℚ
  | .cold => 1
  | .warm => 2/5

private def dominanceTest (t : Temperature) (mask : Fin 8) (bit : Fin 3) : Prop :=
  if mask.val.testBit bit.val then True
  else if bit = 0 then
    marginalThreshold t < lower t mask - upper t (restore mask bit)
  else
    0 < lower t mask - upper t (restore mask bit) ∧
    upper t mask - lower t (restore mask bit) < marginalThreshold t

private instance (t : Temperature) (mask : Fin 8) (bit : Fin 3) :
    Decidable (dominanceTest t mask bit) := by
  unfold dominanceTest
  infer_instance

/-- Every added channel suppresses response. The density suppression
exceeds either other channel's suppression across all tested backgrounds. -/
theorem density_dominance (t : Temperature) (mask : Fin 8) (bit : Fin 3)
    (omitted : mask.val.testBit bit.val = false) :
    let change := response t mask - response t (restore mask bit)
    if bit = 0 then (marginalThreshold t : ℝ) < change
    else 0 < change ∧ change < (marginalThreshold t : ℝ) := by
  have hc : dominanceTest t mask bit := by
    cases t <;> revert mask bit <;> decide +kernel
  have hm := benchmark_bounds t mask
  have hr := benchmark_bounds t (restore mask bit)
  simp only [dominanceTest, omitted, Bool.false_eq_true, if_false] at hc
  dsimp
  by_cases hb : bit = 0
  · subst bit
    simp only [ite_true] at hc ⊢
    have h : (marginalThreshold t : ℝ) <
        (lower t mask : ℝ) - upper t (restore mask 0) := by exact_mod_cast hc
    linarith [hm.1, hr.2]
  · rw [if_neg hb] at hc ⊢
    have h₁ : (0 : ℝ) <
        (lower t mask : ℝ) - upper t (restore mask bit) := by exact_mod_cast hc.1
    have h₂ : (upper t mask : ℝ) - lower t (restore mask bit) <
        marginalThreshold t := by exact_mod_cast hc.2
    exact ⟨by linarith [hm.1, hr.2], by linarith [hm.2, hr.1]⟩

/-- The filled state is an isolated eigenstate at zero source. Its contribution
to the Gibbs trace at the colder benchmark is a single Boltzmann factor. -/
noncomputable def filledProbability (mask : Fin 8) : ℝ :=
  Real.exp ((filledBinding mask : ℝ) / 8) /
    ThermalTrace.partition (hamiltonian mask false 8)

private theorem filled_probability_bounds (mask : Fin 8) (a b l u : ℚ)
    (scale : ℕ) (hs : 0 < scale) (hx : (filledBinding mask : ℚ) / 8 ≤ scale)
    (hx0 : 0 ≤ (filledBinding mask : ℚ) / 8) (ha : 0 < a)
    (hh : (a : ℝ) ≤ ThermalTrace.partition (hamiltonian mask false 8) ∧
      ThermalTrace.partition (hamiltonian mask false 8) ≤ (b : ℝ))
    (hl : 0 ≤ l)
    (hlo : l*b ≤ BCS.expLower ((filledBinding mask : ℚ) / 8) 16 scale)
    (hhi : BCS.expUpper ((filledBinding mask : ℚ) / 8) 16 scale ≤ u*a)
    (hu : 0 ≤ u) :
    (l : ℝ) ≤ filledProbability mask ∧ filledProbability mask ≤ (u : ℝ) := by
  obtain ⟨_, le, ge⟩ := BCS.exp_enclosure _ 16 scale hx0 (by decide) hs hx
  push_cast at le ge
  unfold filledProbability
  have hz := (by exact_mod_cast ha : (0 : ℝ) < a).trans_le hh.1
  exact ⟨(le_div_iff₀ hz).2
      ((mul_le_mul_of_nonneg_left hh.2 (by exact_mod_cast hl)).trans ((by exact_mod_cast hlo :
        (l : ℝ)*b ≤ (BCS.expLower ((filledBinding mask : ℚ) / 8) 16 scale : ℝ)).trans le)),
    (div_le_iff₀ hz).2 (ge.trans ((by exact_mod_cast hhi :
      (BCS.expUpper ((filledBinding mask : ℚ) / 8) 16 scale : ℝ) ≤ (u : ℝ)*a).trans
        (mul_le_mul_of_nonneg_left hh.1 (by exact_mod_cast hu))))⟩

theorem filled_probability_comparison :
    (((162/1000000 : ℚ) : ℝ) ≤ filledProbability 0 ∧ filledProbability 0 ≤ ((163/1000000 : ℚ) : ℝ)) ∧
    (((95820/100000 : ℚ) : ℝ) ≤ filledProbability 1 ∧ filledProbability 1 ≤ ((95822/100000 : ℚ) : ℝ)) ∧
    (((95076/100000 : ℚ) : ℝ) ≤ filledProbability 7 ∧ filledProbability 7 ≤ ((95078/100000 : ℚ) : ℝ)) := by
  constructor
  · exact filled_probability_bounds 0 _ _ (162/1000000) (163/1000000) 8
      (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      m0h0Partition0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · constructor
    · exact filled_probability_bounds 1 _ _ (95820/100000) (95822/100000) 30
        (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        m1h0Partition0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact filled_probability_bounds 7 _ _ (95076/100000) (95078/100000) 30
        (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        m7h0Partition0 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Grain.HubbardChannels
