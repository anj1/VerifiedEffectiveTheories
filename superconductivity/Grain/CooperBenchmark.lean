import Grain.BCSVariational
import Grain.CooperThermal
import Grain.CrystalBCSExample
import Grain.HubbardData.Mask0

/-! The finite four-site Cooper trace and the quadratic approximation use
the same levels, coupling and applied source. The zero-source BCS minimum
alone gives a trial field sufficient to certify failure of the approximation
for the cold pair response. -/

namespace Grain.CrystalBCS.Certificate

open Grain.BCS Grain.HubbardChannels Set

private theorem levels_separated : ∀ i, levels i ≠ 0 := by decide +kernel

private theorem strength_positive : 0 < strength := by decide +kernel

/-- The numerical critical bracket comes from loss of a positive
free-energy minimizer in the quadratic approximation. -/
theorem mean_field_transition : ∃ t ∈ Icc (tLo : ℝ) (tHi : ℝ),
    ∀ T > 0, (∃ d > 0, IsMinOn (meanFieldPotential levels strength T 0) (Ici 0) d) ↔ T < t := by
  obtain ⟨t, ht, h⟩ := thermal_gap_threshold
  refine ⟨t, ht, fun T hT => ?_⟩
  refine Iff.trans ?_ (h T hT)
  exact ⟨fun ⟨d, hd, hm⟩ => ⟨d, hd,
    (thermal_minimum_iff levels strength levels_separated strength_positive hT hd).1 hm⟩,
    fun ⟨d, hd, he⟩ => ⟨d, hd,
    (thermal_minimum_iff levels strength levels_separated strength_positive hT hd).2 he⟩⟩

/-- The zero-temperature amplitude in the certificate minimizes the
quadratic ground energy. -/
theorem mean_field_ground_minimum : ∃ d ∈ Icc (deltaLo : ℝ) (deltaHi : ℝ),
    IsMinOn (meanFieldPotential levels strength 0 0) (Ici 0) d := by
  obtain ⟨d, hd, he, _⟩ := zero_temperature_gap
  have hlo : (0 : ℝ) < deltaLo := by norm_num [deltaLo]
  have hp := hlo.trans_le hd.1
  exact ⟨d, hd, (ground_minimum_iff levels strength levels_separated strength_positive hp).2
    ((zero_gap_equation crystal bands strength attraction_channel hp.ne').1 he)⟩

/-- The signed occupation trace uses the same band energies and Cooper
strength as the variational certificate derived from the site model. -/
theorem cooper_inputs :
    (∀ k : Site, (Grain.HubbardChannels.levels k : ℚ) / 8 = levels k) ∧
      strength = 3/8 := by decide +kernel

/-- The Hamiltonian in meV for the exact Cooper trace. The nonzero source
is 1/20 meV, as encoded in the signed Fock columns. -/
noncomputable def cooperHamiltonian (field : Bool) : Matrix State State ℝ :=
  fun i j => (entry 0 field i j : ℝ) / 40

private def symmetricColumn (field : Bool) (j : State) : Prop :=
  ∀ v ∈ column 0 field j, entry 0 field v.1 j = entry 0 field j v.1

private instance (field : Bool) (j : State) : Decidable (symmetricColumn field j) := by
  unfold symmetricColumn
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
private theorem symmetric_columns (field : Bool) (j : State) : symmetricColumn field j := by
  revert j
  cases field <;> decide +kernel

private theorem entry_zero_of_absent (field : Bool) {i j : State}
    (h : ∀ v ∈ column 0 field j, v.1 ≠ i) : entry 0 field i j = 0 := by
  unfold entry
  apply List.sum_eq_zero
  simp only [List.mem_map]
  rintro _ ⟨v, hv, rfl⟩
  simp [h v hv]

theorem cooper_hamiltonian_symmetric (field : Bool) : (cooperHamiltonian field).IsSymm := by
  ext i j
  change (entry 0 field j i : ℝ) / 40 = (entry 0 field i j : ℝ) / 40
  suffices entry 0 field j i = entry 0 field i j by rw [this]
  by_cases hi : ∃ v ∈ column 0 field i, v.1 = j
  · obtain ⟨v, hv, rfl⟩ := hi
    exact symmetric_columns field i v hv
  by_cases hj : ∃ v ∈ column 0 field j, v.1 = i
  · obtain ⟨v, hv, rfl⟩ := hj
    exact (symmetric_columns field j v hv).symm
  · push Not at hi hj
    rw [entry_zero_of_absent field hi, entry_zero_of_absent field hj]

/-- The finite Cooper grain has an analytic free energy at every positive
temperature, including throughout the quadratic transition bracket. -/
theorem cooper_free_energy_analytic (field : Bool) {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ (Cooper.freeEnergy (cooperHamiltonian field)) t :=
  Cooper.free_energy_analytic (cooper_hamiltonian_symmetric field) ht

/-- The existing rational Taylor bounds apply to the genuine finite Gibbs
free energies of the occupations, with the same source normalization. -/
theorem cooper_response_eq (d : ℕ) (hd : 0 < d) :
    benchmarkResponse 0 d =
      (Cooper.freeEnergy (cooperHamiltonian false) ((d : ℝ)/40) -
        Cooper.freeEnergy (cooperHamiltonian true) ((d : ℝ)/40)) / (2*(1/20 : ℝ)^2) := by
  let t : ℝ := (d : ℝ)/40
  have he (field : Bool) : ThermalTrace.partition (hamiltonian 0 field d) =
      (Cooper.gibbsWeight (cooperHamiltonian field) t).trace := by
    rw [Cooper.checked_partition_eq]
    congr 2
    ext i j
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp [hamiltonian, cooperHamiltonian, t, div_eq_mul_inv]
    ring
  have hp (field : Bool) : 0 < (Cooper.gibbsWeight (cooperHamiltonian field) t).trace :=
    Cooper.partition_pos (cooper_hamiltonian_symmetric field) t
  unfold benchmarkResponse Cooper.freeEnergy
  rw [he true, he false, Real.log_div (hp true).ne' (hp false).ne']
  dsimp [t]
  ring

/-- Real sources are measured in meV and the free-energy difference is
normalized per site by the same factor used in the parent trace. -/
noncomputable def meanFieldResponse (t h : ℝ) : ℝ :=
  (meanFieldFreeEnergy levels strength t 0 - meanFieldFreeEnergy levels strength t h) / (2*h^2)

/-- The exact parent shows a finite positive pair response above and
below the mean-field threshold in the four-site benchmark. -/
theorem cooper_pair_response :
    (5.720669 ≤ benchmarkResponse 0 8 ∧ benchmarkResponse 0 8 ≤ 5.720670) ∧
    (1.942374 ≤ benchmarkResponse 0 20 ∧ benchmarkResponse 0 20 ≤ 1.942375) := by
  exact ⟨by convert m0Response0 using 1 <;> norm_num [m0Response0Lo, m0Response0Hi],
    by convert m0Response1 using 1 <;> norm_num [m0Response1Lo, m0Response1Hi]⟩

/-- At 0.2 meV and source 0.05 meV, dropping the square overestimates
the pair response by more than 19 per site per meV. -/
theorem mean_field_response_excess :
    19 < meanFieldResponse (1/5) (1/20) - benchmarkResponse 0 8 := by
  obtain ⟨d, hd, he, _⟩ := at0_gap
  have hlo : (0.496 : ℝ) ≤ at0DeltaLo := by norm_num [at0DeltaLo]
  have hpos : 0 < d := by linarith [hlo.trans hd.1]
  have ht : (0 : ℝ) < at0 := by norm_num [at0]
  have hmin := (thermal_gap_of_minimum crystal bands strength attraction_channel
    levels_separated strength_positive ht hpos).2 he
  have htrial := mean_field_source_drop levels strength strength_positive ht.le hpos.le hmin (1/20)
  have h := div_le_div_of_nonneg_right htrial (by positivity : 0 ≤ 2 * (1/20 : ℝ)^2)
  have hupper := cooper_pair_response.1.2
  unfold meanFieldResponse
  norm_num [cooper_inputs.2, at0] at h ⊢
  linarith [hlo.trans hd.1]

/-- The discarded-square correction changes by more than 0.095 meV
between zero source and the benchmark source at the cold temperature. -/
theorem fluctuation_cost_change :
    let t : ℝ := 1/5
    0.095 < (meanFieldFreeEnergy levels strength t 0 -
        Cooper.freeEnergy (cooperHamiltonian false) t) -
      (meanFieldFreeEnergy levels strength t (1/20) -
        Cooper.freeEnergy (cooperHamiltonian true) t) := by
  dsimp
  have he := mean_field_response_excess
  rw [cooper_response_eq 8 (by decide)] at he
  norm_num [meanFieldResponse] at he
  linarith

end Grain.CrystalBCS.Certificate
