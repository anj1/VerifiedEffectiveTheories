import VerifiedPhysics.Experiments.WithheldSlab
import VerifiedPhysics.Effective.FiniteSlabCorrection
import VerifiedPhysics.CrossScale.NonlinearSurfaceBound
import VerifiedPhysics.Bulk.NormalModes
import VerifiedPhysics.Atomistic.NonlinearPotential
import VerifiedPhysics.CrossScale.MaxwellSurface
import VerifiedPhysics.CrossScale.MaxwellMatrix
import VerifiedPhysics.Bulk.BiasedResponse
import VerifiedPhysics.Effective.MaxwellPrediction
import VerifiedPhysics.Effective.Reststrahlen
import VerifiedPhysics.CrossScale.HamiltonianBridge
import VerifiedPhysics.Atomistic.Embedding

namespace VerifiedPhysics

/-- A cross-scale comparison for the declared harmonic bulk and finite slab.
The slab check *rejects* the zero-error planar-interface prediction. The
post-test deterministic discrepancy lies strictly between 1/2 and 3/5 in
squared-frequency units. This is a proved finite-size failure, not certified
agreement with the initial prediction. -/
theorem verified_cross_scale_surface_prediction :
    ∃ sMicro sEff k2 x0 x1 : ℝ,
      BulkDielectricLawHolds ∧
      twoCellOperator opticalPattern = 2 • opticalPattern ∧
      EffectiveSurfaceMode sEff k2 ∧
      AtomisticSurfaceMode sMicro k2 x0 x1 ∧
      SurfaceLocalized x0 x1 ∧
      2 < sEff ∧ sEff < 5 ∧ dielectric sEff < 0 ∧
      sEff < k2 ∧
      (1 / 2 : ℝ) < |sMicro - sEff| ∧
      |sMicro - sEff| < (3 / 5 : ℝ) ∧
      ¬ ∃ y0 y1 : ℝ, AtomisticSurfaceMode sEff k2 y0 y1 := by
  refine ⟨observedSquaredFrequency, 3, 6, 2, observedSurfaceAmplitude,
    exact_bulk_dielectric_law, optical_mode_at_zero_wavevector,
    predicted_surface_mode, certified_slab_mode,
    certified_slab_localization, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · exact reststrahlen_negative (by norm_num) (by norm_num)
  · norm_num
  · exact certified_frequency_discrepancy.1
  · exact certified_frequency_discrepancy.2
  · exact predicted_eigenvalue_rejected

/-- After the failed planar prediction, the verified finite-slab correction
predicted a *new*, withheld `k2 = 12` experiment. The directly checked ionic
slab eigenpair lies in the frozen rational prediction interval, with zero
exact-model discrepancy. This success is confined to the specified harmonic
two-layer model and does not cure its missing Coulomb/Maxwell bridges. -/
theorem verified_refined_surface_prediction :
    ∃ sMicro sEff x0 x1 : ℝ,
      (∀ r : Species → Vec3, AdmissiblePosition r →
        nonlinearPotential equilibrium ≤ nonlinearPotential r) ∧
      AxialLinearizationBound ∧
      BulkDielectricLawHolds ∧
      EffectiveSurfaceMode 3 6 ∧
      (¬ ∃ y0 y1 : ℝ, AtomisticSurfaceMode 3 6 y0 y1) ∧
      CorrectedFiniteSlabMode sEff 12 ∧
      AtomisticSurfaceMode sMicro 12 x0 x1 ∧
      SurfaceLocalized x0 x1 ∧
      (287 / 100 : ℝ) < sEff ∧ sEff < (288 / 100 : ℝ) ∧
      |sMicro - sEff| ≤ (0 : ℝ) := by
  refine ⟨7 - Real.sqrt 17, 7 - Real.sqrt 17,
    2, observedSurfaceAmplitude, nonlinear_potential_stable,
    certified_axial_linearization,
    exact_bulk_dielectric_law,
    predicted_surface_mode, predicted_eigenvalue_rejected,
    refined_prediction_at_withheld_wavevector,
    withheld_slab_eigenpair, corrected_mode_localized, ?_, ?_, ?_⟩
  · have h := refined_prediction_interval.1
    rw [← refined_prediction_at_withheld_wavevector.2] at h
    exact h
  · have h := refined_prediction_interval.2
    rw [← refined_prediction_at_withheld_wavevector.2] at h
    exact h
  · norm_num

/-- The strengthened nonlinear-to-harmonic arrow at a nonzero, explicitly
bounded surface displacement. The first conjunct is the actual bulk
constitutive equation, not a Boolean label. The final two conjuncts are
finite-amplitude *force residuals* from the full Coulomb-plus-short-range
potential. They do not assert an eigenfrequency error for nonlinear motion. -/
theorem verified_nonlinear_surface_force_prediction :
    (∀ s E x : ℝ, 0 ≤ s → s ≠ 2 →
      (6 - 3 * s) * x = 3 * E →
      3 * x = ((5 - s) / (2 - s) - 1) * E) ∧
    EffectiveSurfaceMode 3 6 ∧
    CorrectedFiniteSlabMode (7 - Real.sqrt 17) 12 ∧
    AtomisticSurfaceMode (7 - Real.sqrt 17) 12 2 observedSurfaceAmplitude ∧
    SurfaceLocalized 2 observedSurfaceAmplitude ∧
    (let s := 7 - Real.sqrt 17
     let u0 : ℝ := 1 / 50
     let u1 : ℝ := observedSurfaceAmplitude / 100
     0 < u0 ^ 2 + u1 ^ 2 ∧
     SurfaceLocalized u0 u1 ∧
     |deriv (fun y => nonlinearSlabPotential 12 y u1) u0 -
       reducedMass * s * u0| ≤ (2 / 125 : ℝ) * coulombMagnitude ∧
     |deriv (fun y => nonlinearSlabPotential 12 u0 y) u1 -
       reducedMass * s * u1| ≤ (2 / 125 : ℝ) * coulombMagnitude) := by
  refine ⟨?_, predicted_surface_mode,
    refined_prediction_at_withheld_wavevector,
    withheld_slab_eigenpair, corrected_mode_localized,
    withheld_nonlinear_surface_force_residual⟩
  intro s E x hs hne hresponse
  have h := exact_bulk_dielectric_law s E x ⟨hs, hne⟩
    (by dsimp [MicroResponse, spring, reducedMass, charge]; exact hresponse)
  simpa [polarization, dielectric, vacuumPermittivity, charge, cellVolume] using h

/-- The complete finite-model claim. The ionic coefficient of the surface
operator is literally the second derivative of the nonlinear, force-balanced
Coulomb pair potential, divided by its reduced mass. Bulk response gives the
dielectric input to a continuum TM prediction at `(s,k²)=(3,6)`. A separate
32-cell finite Maxwell operator with explicit ionic variables has a localized
mode in `[3.01,3.012]`, uniformly over the declared microscopic strain range.

The frequency discrepancy is strictly nonzero and at most 1/250. The bulk
constitutive error and surface enclosure are deterministic and simultaneous.
This asserts infinitesimal modes about stable biased equilibria, not the
frequency of a finite-amplitude nonlinear periodic orbit or real NaCl. -/
theorem verified_cross_scale_maxwell_surface_prediction (a : ℝ)
    (ha : |a| ≤ (1/1000000000 : ℝ)) :
    let b := deriv (deriv (forceBalancedPotential a)) 0 / reducedMass
    ∃ ωmicro : ℝ, ∃ f : MaxwellSlab.Fields,
      deriv (forceBalancedPotential a) 0 = 0 ∧
      0 < b ∧
      deriv (deriv axialNonlinearPotential) 0 / reducedMass = 2 ∧
      (∀ s E x : ℝ, 0 ≤ s → s ≠ 2 →
        (deriv (deriv axialNonlinearPotential) 0-reducedMass*s)*x = 3*E →
        3*x = ((5-s)/(2-s)-1)*E) ∧
      (∀ s E x : ℝ, s ∈ Set.Icc (3.01 : ℝ) 3.012 →
        (deriv (deriv axialNonlinearPotential) a - reducedMass*s)*x = 3*E →
        |3*x - ((5-s)/(2-s)-1)*E| ≤ (3/1000000 : ℝ)*|E|) ∧
      EffectiveSurfaceMode 3 6 ∧
      (∀ t : ℝ, 2 < t → t < 5 → ∃ decay : ℝ,
        0 < decay ∧ decay^2 = -dielectric t*t ∧
        reflectionReal (Real.sqrt t) decay ^ 2 +
          reflectionImag (Real.sqrt t) decay ^ 2 = 1) ∧
      (∃ av am : ℝ, 0 < av ∧ 0 < am ∧
        TMRegion 1 3 6 (tmMagnetic (-av)) (tmTangential 1 (-av)) (tmNormal 1 (-av)) ∧
        TMRegion (dielectric 3) 3 6 (tmMagnetic am)
          (tmTangential (dielectric 3) am) (tmNormal (dielectric 3) am) ∧
        tmMagnetic (-av) 0 = tmMagnetic am 0 ∧
        tmTangential 1 (-av) 0 = tmTangential (dielectric 3) am 0) ∧
      MaxwellSlab.AtomisticMaxwellEigenmode b (ωmicro^2)
        (MaxwellSlab.electricVector f) (MaxwellSlab.magneticVector f)
        (fun i => MaxwellSlab.overlap i * MaxwellSlab.ionicVector f i) ∧
      MaxwellSlab.overlap (61 : MaxwellSlab.ElectricSite) * MaxwellSlab.ionicVector f 61 ≠ 0 ∧
      (∑ j ∈ Finset.range 8, (f.vacuumH j^2 + f.materialH j^2)) ≤
        (2/5 : ℝ) * (∑ j ∈ Finset.range 16, (f.vacuumH j^2 + f.materialH j^2)) ∧
      ωmicro^2 ∈ Set.Icc (3.01 : ℝ) 3.012 ∧
      0 < ωmicro - Real.sqrt 3 ∧
      |ωmicro - Real.sqrt 3| ≤ (1/250 : ℝ) ∧
      |ωmicro^2 - maxwellPredictedSquaredFrequency| ≤ maxwellPredictedSquaredTolerance := by
  have ha' : -1 < a := by have := (abs_le.mp ha).1; linarith
  have hessian : deriv (deriv (forceBalancedPotential a)) 0 / reducedMass =
      biasedStiffness a := by
    rw [force_balanced_hessian a ha']
    norm_num [reducedMass]
  dsimp only
  rw [hessian]
  have hb := microscopic_stiffness_interval a ha
  obtain ⟨s, f, hs, hf, hloc, hion⟩ := MaxwellSlab.certified_maxwell_ionic_surface _ hb
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hsqrt := Real.sq_sqrt hs0
  have hfreq := MaxwellSlab.frequency_error s hs
  refine ⟨Real.sqrt s, f, force_balanced_equilibrium a ha',
    (by linarith [hb.1]), ?_, ?_, ?_, predicted_surface_mode,
    reststrahlen_unit_reflectivity, frozen_maxwell_prediction_fields,
    ?_, ?_, hloc, ?_, hfreq.1, hfreq.2, ?_⟩
  · rw [microscopic_bulk_hessian]
    norm_num [spring, reducedMass]
  · intro t E x ht htne hresponse
    rw [microscopic_bulk_hessian] at hresponse
    have h := exact_bulk_dielectric_law t E x ⟨ht, htne⟩
      (by simpa [MicroResponse, charge] using hresponse)
    simpa [polarization, dielectric, vacuumPermittivity, charge, cellVolume] using h
  · intro t E x ht hresponse
    exact microscopic_bulk_response_error a t E x ha ht hresponse
  · rw [hsqrt]
    exact MaxwellSlab.stencil_physical_eigenmode _ _ _ hf
  · norm_num [MaxwellSlab.overlap, MaxwellSlab.filling, MaxwellSlab.ionicVector]
    exact hion
  · rwa [hsqrt]
  · rw [hsqrt]
    unfold maxwellPredictedSquaredFrequency maxwellPredictedSquaredTolerance
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2]

end VerifiedPhysics
