import VerifiedPhysics.Experiments.AtomisticGratingGeometry

namespace VerifiedPhysics.GratingExperiment
open MaxwellSlab

/-- Primitive driven TM Maxwell and ionic Newton equations. The only change
from the undriven stencil is the specified source in vacuum cell 15.
No continuum dielectric, transfer matrix, eigenmode or prediction is an input.
Ionic amplitudes at the interface have the original half-cell overlap scaling.
The physical displacements are `overlap i * ionicVector f i`.

The source is a monochromatic magnetic sheet in the retained Fourier sector;
in first-order time-domain Maxwell its amplitude scales as 1/omega under this
second-order forcing convention. Response intensities below are per unit of
this explicitly fixed generalized forcing, not per unit incident power.
-/
def DrivenResponse (b s J : ℝ) (f : Fields) : Prop :=
  (∀ j < 16, f.normalE j + 3 * f.normalIon j = f.materialH j ∧
    (b - s) * f.normalIon j = f.normalE j) ∧
  (∀ j < 15,
    f.vacuumE j = 8 * (f.vacuumH (j+1) - f.vacuumH j) ∧
    f.materialE j + 3 * f.tangentialIon j =
      8 * (f.materialH (j+1) - f.materialH j) ∧
    (b - s) * f.tangentialIon j = f.materialE j) ∧
  f.interfaceE + (3/2 : ℝ) * f.interfaceIon =
    8 * (f.vacuumH 15 - f.materialH 15) ∧
  (b - s) * f.interfaceIon = f.interfaceE ∧
  -8 * f.vacuumE 0 + 6 * f.vacuumH 0 = s * f.vacuumH 0 ∧
  -8 * f.materialE 0 + 6 * f.normalE 0 = s * f.materialH 0 ∧
  (∀ j < 14,
    8 * (f.vacuumE j - f.vacuumE (j+1)) + 6 * f.vacuumH (j+1) =
      s * f.vacuumH (j+1) ∧
    8 * (f.materialE j - f.materialE (j+1)) + 6 * f.normalE (j+1) =
      s * f.materialH (j+1)) ∧
  8 * (f.vacuumE 14 + f.interfaceE) + 6 * f.vacuumH 15 = s * f.vacuumH 15 + J ∧
  8 * (f.materialE 14 - f.interfaceE) + 6 * f.normalE 15 = s * f.materialH 15

/-- Twice the sum of squared magnetic amplitudes/2 in the two cells touching
the interface. A field-enhancement observable, with no flux interpretation. -/
noncomputable def interfaceIntensity (f : Fields) : ℝ :=
  f.vacuumH 15 ^ 2 + f.materialH 15 ^ 2

noncomputable def totalMagneticIntensity (f : Fields) : ℝ :=
  ∑ j ∈ Finset.range 16, (f.vacuumH j ^ 2 + f.materialH j ^ 2)

noncomputable def farMagneticIntensity (f : Fields) : ℝ :=
  ∑ j ∈ Finset.range 8, (f.vacuumH j ^ 2 + f.materialH j ^ 2)

end VerifiedPhysics.GratingExperiment
