import VerifiedPhysics.Atomistic.NonlinearPotential

namespace VerifiedPhysics

/-- The original three-dimensional pair energy in relative coordinates.
The center of mass is a translational zero mode. -/
noncomputable def relativePairPotential (x y z : ℝ) : ℝ :=
  let r := Real.sqrt (x^2+y^2+z^2);
  -coulombMagnitude/r + coulombMagnitude/(2*r^2) +
    ((6-coulombMagnitude)/2)*(r-1)^2 + 3*(x^2+y^2)

theorem relative_potential_bridge (r : Species → Vec3) :
    nonlinearPotential r = relativePairPotential
      (r .cation 0-r .anion 0) (r .cation 1-r .anion 1) (r .cation 2-r .anion 2) := by
  simp [nonlinearPotential, relativePairPotential, bondLength, Fin.sum_univ_three]

theorem even_derivative_zero (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f 0)
    (he : ∀ x, f (-x) = f x) : deriv f 0 = 0 := by
  have hneg : HasDerivAt (fun x : ℝ => f (-x)) (-(deriv f 0)) 0 := by
    have hd : HasDerivAt f (deriv f 0) (-(0:ℝ)) := by simpa using hf.hasDerivAt
    simpa [Function.comp_def] using hd.comp 0 (hasDerivAt_neg (0:ℝ))
  have heq : (fun x : ℝ => f (-x)) = f := funext he
  rw [heq] at hneg
  have h := hneg.deriv
  linarith

/-- The transverse force vanishes exactly on the axial slice. Thus the
retained axial motion is an invariant part of the declared 3D pair model,
when the applied field has the chosen dipole-axis polarization. -/
theorem axial_slice_transverse_forces (a : ℝ) (ha : -1 < a) :
    deriv (fun x => relativePairPotential x 0 (1+a)) 0 = 0 ∧
    deriv (fun y => relativePairPotential 0 y (1+a)) 0 = 0 := by
  have hp : 0 < 1+a := by linarith
  have hs : 0 < (1+a)^2 := by positivity
  constructor
  · apply even_derivative_zero
    · unfold relativePairPotential
      fun_prop (disch := positivity)
    · intro x
      simp [relativePairPotential]
  · apply even_derivative_zero
    · unfold relativePairPotential
      fun_prop (disch := positivity)
    · intro y
      simp [relativePairPotential]

end VerifiedPhysics
