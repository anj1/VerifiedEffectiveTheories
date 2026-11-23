import Grain.PairingParentResponse
import Grain.PairingClosure

/-! Two valid completions of identical projected pairing inputs give
different exact static susceptibilities. -/

namespace Grain.Pairing.ParentResponse

open Grain.HarmonicBand Finset

private def emptyParent : HarmonicBand.Input 2 0 0 where
  levels := fun _ => 0
  density := []
  scattering := []
  screeningConvention := "Two-orbital finite Fock space with a density interaction."
  cartesian := Fin.elim0
  force := Fin.elim0
  vertex := Fin.elim0

/-- The interaction affects the split pair, whose Fock state is omitted
by the same-orbital projection. -/
def densityParent (u : ℚ) : HarmonicBand.Input 2 0 0 := Material.addSplitPairDensity emptyParent u

theorem density_parent_valid (u : ℚ) : Valid (densityParent u) :=
  Material.add_split_pair_density_valid emptyParent (by decide +kernel) u

theorem density_parents_same_projection (u v : ℚ) :
    Material.parentRealization (densityParent u) 0 =
      Material.parentRealization (densityParent v) 0 := by
  have hc : (fun i j => (Material.parentCoulomb (densityParent u) i j : ℝ)) =
      fun i j => (Material.parentCoulomb (densityParent v) i j : ℝ) := by
    funext i j
    exact congrArg Rat.cast ((Material.add_split_pair_density_projection emptyParent u i j).trans
      (Material.add_split_pair_density_projection emptyParent v i j).symm)
  unfold Material.parentRealization
  change Material.Realization.mk _ _ (fun i j => (Material.parentCoulomb (densityParent u) i j : ℝ)) _ =
    Material.Realization.mk _ _ (fun i j => (Material.parentCoulomb (densityParent v) i j : ℝ)) _
  rw [hc]
  rfl

private def splitOccupied (s : State 2) : Bool := occupied s (0, 0) && occupied s (1, 1)

/-- The full electronic eigenbasis is the occupation basis. -/
theorem density_parent_diagonal (u : ℚ) (i j : State 2) :
    electronic (densityParent u) i j = if i = j ∧ splitOccupied j then u else 0 := by
  by_cases hi : i = j <;> cases h₁ : occupied j (0, 0) <;> cases h₂ : occupied j (1, 1) <;>
    simp [electronic, kinetic, screened, densityParent, Material.addSplitPairDensity,
      emptyParent, splitOccupied, hi, h₁, h₂, scatteringColumn, columnEntry]

private def eigenEnergy (u : ℚ) (i : State 2) : ℝ := (electronic (densityParent u) i i : ℝ)

private theorem eigen_energy (u : ℚ) (i : State 2) :
    eigenEnergy u i = if splitOccupied i then (u : ℝ) else 0 := by
  rw [eigenEnergy, density_parent_diagonal]
  simp
  split <;> simp

private def paired : State 2 := Material.pairState 0

/-- A source that creates or annihilates a pair in orbital zero with the
spectator orbital empty. The sign of its only nonzero matrix element
depends on the phase convention and drops out of the response. -/
def vacuumPairSource (i j : State 2) : ℝ :=
  if (i = 0 ∧ j = paired) ∨ (i = paired ∧ j = 0) then 1 else 0

private theorem vacuum_pair_numerator (β : ℝ) (u : ℚ) :
    responseSum β (eigenEnergy u) vacuumPairSource Finset.univ = 2 := by
  have hp : paired ≠ 0 := by decide +kernel
  have hp0 : (0 : State 2) ≠ paired := Ne.symm hp
  have h0 : eigenEnergy u 0 = 0 := by
    rw [eigen_energy]
    rfl
  have h1 : eigenEnergy u paired = 0 := by
    rw [eigen_energy]
    rfl
  have hweight : transitionWeight β 0 0 = 1 := by
    rw [transition_weight_self]
    simp [gibbsFactor]
  have hrow (i : State 2) :
      ∑ j : State 2, transitionWeight β (eigenEnergy u i) (eigenEnergy u j) *
          vacuumPairSource i j ^ 2 = (if i = 0 then 1 else 0) + (if i = paired then 1 else 0) := by
    by_cases hi : i = 0
    · subst i
      simp only [vacuumPairSource, hp0, true_and, false_and, or_false, ite_true, ite_false, add_zero, h0]
      rw [sum_eq_single paired]
      · simp [h1, hweight]
      · intro j _ hj
        simp [hj]
      · simp
    · by_cases hj : i = paired
      · subst i
        simp only [vacuumPairSource, hp, false_and, true_and, false_or, ite_true, ite_false, zero_add, h1]
        rw [sum_eq_single 0]
        · simp [h0, hweight]
        · intro j _ hj
          simp [hj]
        · simp
      · simp [vacuumPairSource, hi, hj]
  unfold responseSum
  simp_rw [hrow, sum_add_distrib]
  norm_num

private theorem density_parent_partition (β : ℝ) (u : ℚ) :
    (∑ i, gibbsFactor β (eigenEnergy u i)) = 12 + 4 * gibbsFactor β u := by
  have hocc : (Finset.univ.filter fun i : State 2 => splitOccupied i).card = 4 := by
    decide +kernel
  have hfree : (Finset.univ.filter fun i : State 2 => ¬ splitOccupied i).card = 12 := by
    decide +kernel
  simp_rw [eigen_energy, apply_ite (gibbsFactor β), show gibbsFactor β 0 = 1 by simp [gibbsFactor]]
  rw [Finset.sum_ite, sum_const, sum_const, hocc, hfree, nsmul_eq_mul, nsmul_eq_mul]
  norm_num
  ring

/-- Exact grand-canonical susceptibility of the specified finite parent
to the chosen real pair source. The zero-source expectation vanishes
since the source is off diagonal in the occupation basis. -/
noncomputable def exactPairResponse (β : ℝ) (u : ℚ) : ℝ :=
  susceptibility β (eigenEnergy u) vacuumPairSource

theorem exact_pair_response (β : ℝ) (u : ℚ) :
    exactPairResponse β u = (2 * β) / (12 + 4 * Real.exp (-β * u)) := by
  rw [exactPairResponse, susceptibility_fintype, vacuum_pair_numerator, density_parent_partition,
    gibbsFactor]
  ring

/-- Equal projected pairing inputs can conceal a change in the exact
thermal observable, even before any oscillator or frequency truncation. -/
theorem exact_pair_response_changes {β : ℝ} (hβ : 0 < β) {u : ℚ} (hu : 0 < u) :
    Material.parentRealization (densityParent u) 0 =
      Material.parentRealization (densityParent 0) 0 ∧
      exactPairResponse β 0 < exactPairResponse β u := by
  refine ⟨density_parents_same_projection u 0, ?_⟩
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have he : Real.exp (-β * u) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hβ hu'])
  simp_rw [exact_pair_response]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  norm_num
  rw [neg_mul] at he
  linarith only [he]

end Grain.Pairing.ParentResponse
