import VerifiedPhysics.Prediction.FrozenScatteringPrediction
import VerifiedPhysics.Experiments.ScatteringCertificate
import VerifiedPhysics.CrossScale.DrivenMaxwellMatrix
import VerifiedPhysics.Atomistic.BiasedHessian

namespace VerifiedPhysics
open MaxwellSlab GratingExperiment

theorem scattering_hessian_identification :
    deriv (deriv (forceBalancedPotential 0)) 0 / reducedMass = 2 := by
  rw [force_balanced_hessian 0 (by norm_num), biased_stiffness_zero]
  norm_num [reducedMass]

theorem selected_geometry_is_tested_geometry :
    ScatteringPrediction.selectedPeriod = GratingExperiment.period ∧
    2 * Real.pi / GratingExperiment.period = Real.sqrt 6 ∧
    (∀ m : ℤ, 0 < m → ScatteringPrediction.selectedOrder ≤ m) := by
  refine ⟨rfl, proposed_grating_reciprocal_vector, ?_⟩
  intro m hm
  change 1 ≤ m
  omega

/-- Validation of the unchanged frozen amplitude hypothesis. The observable
is fixed for every primitive solution, not just for the supplied witnesses. -/
theorem frozen_scattering_prediction_validated :
    DrivenResponse 2 ScatteringPrediction.driveSquaredFrequency 1 resonant ∧
    DrivenResponse 2 ScatteringPrediction.controlSquaredFrequency 1 control ∧
    ScatteringPrediction.minimumIntensity ≤ interfaceIntensity resonant ∧
    ScatteringPrediction.minimumContrast * interfaceIntensity control ≤
      interfaceIntensity resonant ∧
    interfaceIntensity control + (3/4 : ℝ) ≤ interfaceIntensity resonant ∧
    (∀ f : Fields, DrivenResponse 2 3 1 f → interfaceIntensity f = interfaceIntensity resonant) ∧
    (∀ f : Fields, DrivenResponse 2 4 1 f → interfaceIntensity f = interfaceIntensity control) := by
  refine ⟨resonant_equations, control_equations, resonant_intensity, ?_, ?_, ?_, ?_⟩
  · change 4 * interfaceIntensity control ≤ interfaceIntensity resonant
    linarith [resonant_intensity, control_intensity]
  · linarith [resonant_intensity, control_intensity]
  · intro f hf
    obtain ⟨hv, hm⟩ := resonant_interface_unique f hf
    simp only [interfaceIntensity, hv, hm]
  · intro f hf
    obtain ⟨hv, hm⟩ := control_interface_unique f hf
    simp only [interfaceIntensity, hv, hm]

/-- The observed eigenmode interval is contained in the frozen frequency
budget; its width is 1/500 in squared-frequency units. This is a finite-model
comparison, not a grid-convergence theorem or an amplitude-error estimate. -/
theorem observed_interval_within_frozen_budget (s : ℝ)
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    s ∈ ScatteringPrediction.predictedSquaredInterval ∧
    |s - 3| ≤ ScatteringPrediction.finiteSlabSquaredAllowance ∧
    (3.012 : ℝ) - 3.01 = 1/500 := by
  have h : |s - 3| ≤ (3/100 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨ScatteringPrediction.budget_interval_containment s ?_, h, by norm_num⟩
  simpa [ScatteringPrediction.driveSquaredFrequency, ScatteringPrediction.bulkError,
    ScatteringPrediction.continuumError, ScatteringPrediction.finiteSlabSquaredAllowance,
    ScatteringPrediction.numericalError] using h

/-- Immediately readable primitive equations for either certified driven
experiment: 32 magnetic rows, 63 electric rows, explicit ionic displacements.
The occupied subset consists of 32 ionic pairs (64 physical ions). -/
theorem verified_driven_ionic_maxwell_equations :
    ∀ (s : ℝ) (f : Fields),
      (s = 3 ∧ f = resonant) ∨ (s = 4 ∧ f = control) →
      (∀ j : Fin 32, (∑ i : Fin 63, curlMatrix j i * electricVector f i) =
        s * magneticVector f j + (if j = 15 then 1 else 0)) ∧
      (∀ i : Fin 63, (∑ j : Fin 32, curlMatrix j i * magneticVector f j) =
        electricVector f i + 3 * overlap i * (overlap i * ionicVector f i)) ∧
      (∀ i : Fin 63, (deriv (deriv (forceBalancedPotential 0)) 0 / reducedMass-s) *
        (overlap i * ionicVector f i) = overlap i * electricVector f i) := by
  intro s f h
  rw [scattering_hessian_identification]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact driven_physical_equations 2 3 1 resonant resonant_equations
  · exact driven_physical_equations 2 4 1 control control_equations

end VerifiedPhysics
