import VerifiedPhysics.Atomistic.AxialForce

namespace VerifiedPhysics

/-- Local small-oscillation stiffness of the nonlinear Coulomb pair about
axial bias `a`, divided by the reduced mass. A constant external force holds
that bias; its linear potential has zero Hessian. -/
noncomputable def biasedStiffness (a : ℝ) : ℝ :=
  (6 - coulombMagnitude + coulombMagnitude * (1 - 2 * a) / (1 + a) ^ 4) / 3

theorem biased_stiffness_is_hessian (a : ℝ) (ha : -1 < a) :
    deriv axialNonlinearGradient a = reducedMass * biasedStiffness a := by
  have hn : 1 + a ≠ 0 := by linarith
  have hd : HasDerivAt (fun x : ℝ => 1 + x) 1 a := by
    convert (hasDerivAt_id a).const_add 1 using 1
    funext x; rfl
  have hi := hd.inv hn
  have h2 := (hi.pow 2).const_mul coulombMagnitude
  have h3 := (hi.pow 3).const_mul coulombMagnitude
  have hl := (hasDerivAt_id a).const_mul (6 - coulombMagnitude)
  have h := (h2.sub h3).add hl
  have hf : axialNonlinearGradient =
      ((fun x : ℝ => coulombMagnitude * ((1 + x)⁻¹)^2) -
        (fun x : ℝ => coulombMagnitude * ((1 + x)⁻¹)^3)) +
        (fun x : ℝ => (6 - coulombMagnitude) * x) := by
    funext x
    dsimp [axialNonlinearGradient]
    simp only [inv_pow, div_eq_mul_inv]
  have h' := h.deriv
  change deriv (((fun x : ℝ => coulombMagnitude * ((1+x)⁻¹)^2) -
    (fun x : ℝ => coulombMagnitude * ((1+x)⁻¹)^3)) +
    (fun x : ℝ => (6-coulombMagnitude)*x)) a = _ at h'
  rw [hf, h']
  dsimp [biasedStiffness, reducedMass]
  field_simp [hn]
  ring

/-- The Hessian is the actual second derivative of the original potential,
not merely the derivative of a separately introduced force formula. -/
theorem nonlinear_second_derivative (a : ℝ) (ha : -1 < a) :
    deriv (deriv axialNonlinearPotential) a = reducedMass * biasedStiffness a := by
  have hlocal : deriv axialNonlinearPotential =ᶠ[nhds a] axialNonlinearGradient := by
    filter_upwards [Ioi_mem_nhds ha] with x hx
    exact axial_gradient_eq_deriv x hx
  rw [hlocal.deriv_eq]
  exact biased_stiffness_is_hessian a ha

theorem biased_stiffness_zero : biasedStiffness 0 = 2 := by
  norm_num [biasedStiffness]

theorem microscopic_bulk_hessian :
    deriv (deriv axialNonlinearPotential) 0 = spring := by
  rw [nonlinear_second_derivative 0 (by norm_num), biased_stiffness_zero]
  norm_num [reducedMass, spring]

/-- A static force balances the microscopic strain `a`. Its linear potential
does not alter the Hessian. The perturbation coordinate is `x`. -/
noncomputable def forceBalancedPotential (a x : ℝ) : ℝ :=
  axialNonlinearPotential (a+x) - axialNonlinearPotential a -
    axialNonlinearGradient a * x

theorem force_balanced_derivative (a x : ℝ) (hx : -1 < a+x) :
    deriv (forceBalancedPotential a) x =
      axialNonlinearGradient (a+x) - axialNonlinearGradient a := by
  have hp : 0 < 1+(a+x) := by linarith
  have hd : DifferentiableAt ℝ axialNonlinearPotential (a+x) := by
    unfold axialNonlinearPotential
    fun_prop (disch := positivity)
  have h := (hd.hasDerivAt.comp x ((hasDerivAt_id x).const_add a)).sub_const
    (axialNonlinearPotential a)
  have h' := h.sub ((hasDerivAt_id x).const_mul (axialNonlinearGradient a))
  have heq : deriv (forceBalancedPotential a) x =
      deriv axialNonlinearPotential (a+x) - axialNonlinearGradient a := by
    convert h'.deriv using 1
    · congr 1
    · simp
  rw [heq, axial_gradient_eq_deriv (a+x) hx]

theorem force_balanced_equilibrium (a : ℝ) (ha : -1 < a) :
    deriv (forceBalancedPotential a) 0 = 0 := by
  rw [force_balanced_derivative a 0 (by simpa using ha)]
  simp

theorem force_balanced_hessian (a : ℝ) (ha : -1 < a) :
    deriv (deriv (forceBalancedPotential a)) 0 = reducedMass * biasedStiffness a := by
  have hlocal : deriv (forceBalancedPotential a) =ᶠ[nhds (0 : ℝ)]
      (fun x => axialNonlinearGradient (a+x)-axialNonlinearGradient a) := by
    filter_upwards [Ioi_mem_nhds (by linarith : -1-a < (0:ℝ))] with x hx
    change -1-a < x at hx
    exact force_balanced_derivative a x (by linarith)
  rw [hlocal.deriv_eq, deriv_sub_const]
  have hp : 0 < 1+a := by linarith
  have hd : DifferentiableAt ℝ axialNonlinearGradient a := by
    unfold axialNonlinearGradient
    fun_prop (disch := positivity)
  have hd' : HasDerivAt axialNonlinearGradient (deriv axialNonlinearGradient a) (a+0) :=
    by simpa using hd.hasDerivAt
  have h := hd'.comp 0 ((hasDerivAt_id (0:ℝ)).const_add a)
  have heq : deriv (fun x => axialNonlinearGradient (a+x)) 0 =
      deriv axialNonlinearGradient a := by
    simpa [Function.comp_def] using h.deriv
  rw [heq, biased_stiffness_is_hessian a ha]

theorem biased_stiffness_remainder (a : ℝ) (ha : -1 < a) :
    biasedStiffness a - 2 =
      -coulombMagnitude * a * (6 + 6 * a + 4 * a ^ 2 + a ^ 3) /
        (3 * (1 + a) ^ 4) := by
  have hn : 1 + a ≠ 0 := by linarith
  unfold biasedStiffness
  field_simp [hn]
  ring

theorem biased_stiffness_bound (a : ℝ) (ha : |a| ≤ (1 / 2 : ℝ)) :
    |biasedStiffness a - 2| ≤ 64 * coulombMagnitude * |a| := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  have hlo' : -0.5 ≤ a := by linarith
  have hhi' : a ≤ 0.5 := by linarith
  have hp : 0 < 3 * (1 + a)^4 := by
    have : 0 < 1 + a := by linarith
    positivity
  have hq : 0 ≤ 6 + 6 * a + 4 * a ^ 2 + a ^ 3 := by
    simp only [pow_succ, pow_zero]
    dyadic_interval [prec := 20]
  have hr : (6 + 6 * a + 4 * a ^ 2 + a ^ 3) / (3 * (1 + a)^4) ≤ (64 : ℝ) := by
    apply (div_le_iff₀ hp).2
    simp only [pow_succ, pow_zero]
    dyadic_interval [prec := 20]
  rw [biased_stiffness_remainder a (by linarith)]
  have hc : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  calc
    _ = coulombMagnitude * |a| *
        ((6 + 6 * a + 4 * a ^ 2 + a ^ 3) / (3 * (1 + a)^4)) := by
      rw [abs_div, abs_mul, abs_mul, abs_neg, abs_of_nonneg hc,
        abs_of_nonneg hq, abs_of_pos hp]
      ring
    _ ≤ coulombMagnitude * |a| * 64 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

theorem microscopic_stiffness_interval (a : ℝ)
    (ha : |a| ≤ (1 / 1000000000 : ℝ)) :
    biasedStiffness a ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ) := by
  have hb := biased_stiffness_bound a (by linarith)
  have hc : 0 ≤ coulombMagnitude := le_of_lt coulomb_magnitude_positive
  have he : |biasedStiffness a - 2| ≤ (1 / 1000000 : ℝ) := by
    calc
      _ ≤ 64 * coulombMagnitude * |a| := hb
      _ ≤ 64 * 1 * (1 / 1000000000 : ℝ) := by
        gcongr
        exact le_of_lt coulomb_magnitude_lt_one
      _ ≤ _ := by norm_num
  constructor <;> linarith [(abs_le.mp he).1, (abs_le.mp he).2]

end VerifiedPhysics
