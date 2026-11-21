import Grain.PhononElectronic
import Grain.PhononHamiltonian

/-! Sector comparisons for the specified spinful electron–phonon Hamiltonian. -/

namespace Grain.Phonon

open TwoShell
open scoped BigOperators

/-- The shifted reduced-BCS ground energy bounds every Rayleigh quotient of
the primitive harmonic Hamiltonian. The upper bound uses a dressed trial in
the actual spinful sector. -/
theorem microscopic_sector_comparison (r s : Bool) (k : Fin 3) :
    Prediction.energy r s k + electronicShift k ≤ microscopicGround r s k ∧
      microscopicGround r s k ≤ Prediction.energy r s k + electronicShift k + phononTolerance := by
  let K := kineticForm (Prediction.innerRadius r) (Prediction.outerRadius s) (n := 6 + k.val)
  let l := Prediction.energy r s k + electronicShift k
  let u := ((FullSolve.witness r s k).hi : ℝ) + electronicShift k
  have hl : ∀ v, l * normSq v ≤ effective K vertex frequency mixing v :=
    electronic_lower r s k
  have hω : 0 ≤ frequency := by norm_num [frequency]
  have hK0 : K 0 = 0 := by simp [K, kineticForm]
  obtain ⟨x, hx, hu⟩ := electronic_trial r s k
  have hK := kinetic_le r s k
  have hB : vertexNorm vertex x ≤ 112 := by simpa [hx] using vertexNorm_le x
  obtain ⟨hu0, hu1, huGap⟩ := shifted_upper_budget r s k
  have hu0' : -81 ≤ u := hu0
  have hu1' : u ≤ 80 := hu1
  have budget : mixing ^ 2 * 112 * (80 - u) ≤ 19 / 10^13 := by
    norm_num [mixing]
    linarith
  have lb : ∀ e ∈ microscopicEnergies r s k, l ≤ e := by
    intro e he
    obtain ⟨cutoff, hcutoff⟩ := Set.mem_iUnion.mp he
    obtain ⟨ψ, hp, rfl⟩ := hcutoff
    apply (le_div_iff₀ hp).2
    exact harmonic_lower K vertex frequency mixing l hω hl ψ (fun j => annihilate j ψ)
  have oneMember : (normalizedEnergies (phononHamiltonian r s k 0)).Nonempty := by
    let ψ := lowState (m := Mode) (p := HigherQuanta 0) x (fun _ => 0)
    refine ⟨_, ψ, ?_, rfl⟩
    simp [ψ, lowState, Fintype.sum_sum_type, Fintype.sum_option, normSq_zero, hx]
  have subset : normalizedEnergies (phononHamiltonian r s k 0) ⊆ microscopicEnergies r s k :=
    fun _ he => Set.mem_iUnion.mpr ⟨0, he⟩
  have nonempty := oneMember.mono subset
  have hbelow : BddBelow (microscopicEnergies r s k) := ⟨l, lb⟩
  have hbox : microscopicGround r s k ≤ sInf (normalizedEnergies (phononHamiltonian r s k 0)) :=
    le_csInf oneMember (fun _ he => csInf_le hbelow (subset he))
  have upperBox := (harmonic_ground_bounds K vertex (annihilate (cutoff := 0))
    frequency mixing l u 80 112 (19 / 10^13) hω hK0 hl x hx hu hK hB
    (sub_nonneg.mpr hu1') (by norm_num) budget
    (fun j => annihilate_low x (dressing vertex mixing x) j)).2
  change sInf (normalizedEnergies (phononHamiltonian r s k 0)) ≤ u + 19 / 10^13 at upperBox
  refine ⟨le_csInf nonempty lb, hbox.trans (upperBox.trans ?_)⟩
  unfold phononTolerance
  change u ≤ l + 1 / 10^13 at huGap
  linarith

/-- Each microscopic energy also has explicit endpoints from the retained
reduced-BCS certificate and the harmonic comparison. -/
theorem microscopic_sector_enclosure (r s : Bool) (k : Fin 3) :
    (FullSolve.witness r s k).lo + electronicShift k ≤ microscopicGround r s k ∧
      microscopicGround r s k ≤ (FullSolve.witness r s k).hi + electronicShift k + phononTolerance := by
  obtain ⟨l, u⟩ := microscopic_sector_comparison r s k
  obtain ⟨l', u'⟩ := FullSolve.sector_bounds r s k
  constructor <;> linarith

/-- All twelve ground energies are the variational energies of the declared
microscopic Hamiltonian. Their one-sided sector error implies the positive
mixed shell contrast. -/
theorem verified_phonon_comparison :
    (∀ r s k, Prediction.energy r s k + electronicShift k ≤ microscopicGround r s k ∧
      microscopicGround r s k ≤ Prediction.energy r s k + electronicShift k + phononTolerance) ∧
    0 < microscopicContrast microscopicGround ∧
      |microscopicContrast microscopicGround - Prediction.mixedContrast| ≤ 4 * phononTolerance :=
  ⟨microscopic_sector_comparison, microscopic_contrast_positive _ microscopic_sector_comparison⟩

end Grain.Phonon
