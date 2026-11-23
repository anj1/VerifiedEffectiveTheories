import Grain.BCSThermal
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The free energy of the finite quadratic Cooper approximation. The total
pair field includes the source. At zero temperature the single-level term
is the lowest energy among the two paired and two blocked states. -/

namespace Grain.BCS

open Set

variable {ι : Type}

noncomputable def levelFreeEnergy (xi t x : ℝ) : ℝ :=
  let E := quasiparticle xi x
  xi - E - if t = 0 then 0 else 2 * t * Real.log (1 + Real.exp (-E / t))

noncomputable def meanFieldPotential [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (t eta x : ℝ) : ℝ :=
  (x - eta)^2 / (g : ℝ) + ∑ i, levelFreeEnergy (xi i : ℝ) t x

noncomputable def meanFieldFreeEnergy [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (t eta : ℝ) : ℝ :=
  sInf (meanFieldPotential xi g t eta '' Ici 0)

/-- The empty/doubly occupied block has diagonal entries `0, 2ξ`
and pair-transfer entries `-x`. Its secular polynomial has roots `ξ ± E`. -/
theorem paired_block_characteristic (xi x e : ℝ) :
    (-e) * (2*xi-e) - x^2 =
      (e - (xi - quasiparticle xi x)) * (e - (xi + quasiparticle xi x)) := by
  have hE : quasiparticle xi x ^ 2 = xi^2 + x^2 :=
    Real.sq_sqrt (by positivity)
  nlinarith only [hE]

/-- The four Fock energies are `ξ-E, ξ+E, ξ, ξ`. The two blocked
states supply the middle term of the squared partition factor. -/
theorem level_free_energy_of_spectrum (xi x : ℝ) {t : ℝ} (ht : 0 < t) :
    let E := quasiparticle xi x
    levelFreeEnergy xi t x =
      -t * Real.log (Real.exp (-(xi-E)/t) + Real.exp (-(xi+E)/t) + 2 * Real.exp (-xi/t)) := by
  intro E
  have eq : Real.exp (-(xi-E)/t) + Real.exp (-(xi+E)/t) + 2 * Real.exp (-xi/t) =
      Real.exp (-(xi-E)/t) * (1 + Real.exp (-E/t))^2 := by
    have hm : Real.exp (-(xi-E)/t) * Real.exp (-E/t) = Real.exp (-xi/t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hp : Real.exp (-(xi-E)/t) * Real.exp (-E/t)^2 = Real.exp (-(xi+E)/t) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    rw [add_sq, mul_add, mul_add, mul_one 2, mul_left_comm (Real.exp _) 2 _, hm, hp]
    ring
  rw [eq, Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp, Real.log_pow]
  simp only [levelFreeEnergy, ht.ne', ite_false, E]
  field_simp
  ring

private theorem quasiparticle_derivative {xi : ℝ} (hxi : xi ≠ 0) (x : ℝ) :
    HasDerivAt (quasiparticle xi) (x / quasiparticle xi x) x := by
  have h := ((hasDerivAt_pow 2 x).const_add (xi^2)).sqrt
    (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hxi) (sq_nonneg x)).ne'
  convert h using 1
  · rfl
  · simp only [Nat.reduceSubDiff, pow_one, Nat.cast_ofNat, quasiparticle]
    ring

/-- The scalar response uses the ground-state weight at zero temperature. -/
noncomputable def gapResponse [Fintype ι] (xi : ι → ℚ) (g : ℚ) (t x : ℝ) : ℝ :=
  if t = 0 then zeroResponse xi g x else thermalResponse xi g t x

private theorem level_derivative {xi : ℝ} (hxi : xi ≠ 0) (t x : ℝ) :
    HasDerivAt (levelFreeEnergy xi t)
      (-2 * x * (if t = 0 then 1 / (2 * quasiparticle xi x)
        else thermalSusceptibility (quasiparticle xi x) t)) x := by
  let E := quasiparticle xi x
  have he : 0 < E := quasiparticle_pos hxi x
  have hd := quasiparticle_derivative hxi x
  by_cases ht : t = 0
  · subst t
    unfold levelFreeEnergy
    simp only [ite_true, sub_zero]
    convert hd.const_sub xi using 1
    change -2 * x * (1 / (2 * E)) = -(x / E)
    ring
  · have hexp := (hd.neg.div_const t).exp.const_add 1
    have hlog := hexp.log (by positivity : 1 + Real.exp (-E/t) ≠ 0)
    unfold levelFreeEnergy
    simp only [ht, ite_false]
    convert (hd.const_sub xi).sub (hlog.const_mul (2*t)) using 1
    change -2 * x * thermalSusceptibility E t =
      -(x / E) - 2*t * (Real.exp (-E/t) * (-(x/E)/t) / (1 + Real.exp (-E/t)))
    rw [thermalSusceptibility, thermalFactor, show -E / t = -(E / t) by ring, Real.exp_neg]
    have hp := Real.exp_pos (E / t)
    field_simp
    ring

theorem mean_field_derivative [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : g ≠ 0) (t eta x : ℝ) :
    HasDerivAt (meanFieldPotential xi g t eta)
      (2 / (g : ℝ) * (x * (1 - gapResponse xi g t x) - eta)) x := by
  have h : HasDerivAt (fun y : ℝ => (y-eta)^2 / (g : ℝ)) (2*(x-eta)/(g : ℝ)) x := by
    simpa using (((hasDerivAt_id x).sub_const eta).pow 2).div_const (g : ℝ)
  have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast hg
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) fun i _ =>
    level_derivative (xi := (xi i : ℝ)) (by exact_mod_cast hxi i) t x
  convert h.add hsum using 1
  · rfl
  unfold gapResponse
  split <;> simp only [zeroResponse, thermalResponse,
    ← Finset.mul_sum] <;> field_simp <;> ring

private theorem mean_field_continuous [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : g ≠ 0) (t eta : ℝ) : Continuous (meanFieldPotential xi g t eta) :=
  continuous_iff_continuousAt.mpr fun x => (mean_field_derivative xi g hxi hg t eta x).continuousAt

private theorem gap_response_decreases [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t : ℝ} (ht : 0 ≤ t) :
    StrictAntiOn (gapResponse xi g t) (Ici 0) := by
  by_cases hz : t = 0
  · intro x hx y hy hxy
    simpa [gapResponse, hz] using zero_decreases xi g hxi hg hx hy hxy
  · intro x hx y hy hxy
    simpa [gapResponse, hz] using thermal_decreases xi g hxi hg (lt_of_le_of_ne ht (Ne.symm hz))
      hx hy hxy

/-- A positive zero-source minimum solves the gap equation. Conversely the
strict decrease of the response gives a unique minimizing magnitude. -/
theorem positive_minimum_iff [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    IsMinOn (meanFieldPotential xi g t 0) (Ici 0) x ↔ gapResponse xi g t x = 1 := by
  have hg' : 0 < (g : ℝ) := by exact_mod_cast hg
  have hd (y : ℝ) := (mean_field_derivative xi g hxi hg.ne' t 0 y).deriv
  have hc := mean_field_continuous xi g hxi hg.ne' t 0
  have hm := gap_response_decreases xi g hxi hg ht
  constructor
  · intro h
    have hl : IsLocalMin (meanFieldPotential xi g t 0) x :=
      h.isLocalMin (Ici_mem_nhds hx)
    have hz := hl.deriv_eq_zero
    rw [hd, sub_zero, mul_eq_zero, mul_eq_zero] at hz
    have he : 1 - gapResponse xi g t x = 0 :=
      (hz.resolve_left (by positivity)).resolve_left hx.ne'
    linarith
  · intro h
    have hleft : StrictAntiOn (meanFieldPotential xi g t 0) (Icc 0 x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc ..) hc.continuousOn
      intro y hy
      rw [interior_Icc] at hy
      have hr := hm hy.1.le hx.le hy.2
      rw [h] at hr
      rw [hd, sub_zero]
      exact mul_neg_of_pos_of_neg (by positivity) (mul_neg_of_pos_of_neg hy.1 (by linarith))
    have hright : StrictMonoOn (meanFieldPotential xi g t 0) (Ici x) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici _) hc.continuousOn
      intro y hy
      rw [interior_Ici] at hy
      have hr := hm hx.le (hx.trans hy).le hy
      rw [h] at hr
      rw [hd, sub_zero]
      exact mul_pos (by positivity) (mul_pos (hx.trans hy) (by linarith))
    intro y hy
    rcases le_total y x with hle | hle
    · exact hleft.antitoneOn ⟨hy, hle⟩ ⟨hx.le, le_rfl⟩ hle
    · exact hright.monotoneOn (mem_Ici.mpr le_rfl) hle hle

theorem thermal_minimum_iff [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    IsMinOn (meanFieldPotential xi g t 0) (Ici 0) x ↔ thermalResponse xi g t x = 1 := by
  simpa [gapResponse, ht.ne'] using positive_minimum_iff xi g hxi hg ht.le hx

theorem ground_minimum_iff [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {x : ℝ} (hx : 0 < x) :
    IsMinOn (meanFieldPotential xi g 0 0) (Ici 0) x ↔ zeroResponse xi g x = 1 := by
  simpa [gapResponse] using positive_minimum_iff xi g hxi hg (t := 0) le_rfl hx

private theorem level_lower_bound (xi : ℝ) {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    xi - |xi| - x - 2*t*Real.log 2 ≤ levelFreeEnergy xi t x := by
  have hE : quasiparticle xi x ≤ |xi| + x := by
    unfold quasiparticle
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have h := mul_nonneg (abs_nonneg xi) hx
    nlinarith [sq_abs xi]
  by_cases hz : t = 0
  · simp [levelFreeEnergy, hz]
    linarith
  · have hlog : Real.log (1 + Real.exp (-quasiparticle xi x / t)) ≤ Real.log 2 := by
      apply Real.log_le_log (by positivity)
      have hq : Real.exp (-quasiparticle xi x / t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (by unfold quasiparticle; positivity)) ht)
      linarith
    simp only [levelFreeEnergy, hz, ite_false]
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*t by positivity)
    linarith

private theorem potential_bddBelow [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (hg : 0 < g) {t : ℝ} (ht : 0 ≤ t) (eta : ℝ) :
    BddBelow (meanFieldPotential xi g t eta '' Ici 0) := by
  let n : ℝ := Fintype.card ι
  let a : ℝ := n * (g : ℝ) / 2
  let c : ℝ := ∑ i, ((xi i : ℝ) - |(xi i : ℝ)| - 2*t*Real.log 2)
  have hg' : 0 < (g : ℝ) := by exact_mod_cast hg
  refine ⟨c - n * eta - a^2/(g : ℝ), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hs : c - n*x ≤ ∑ i, levelFreeEnergy (xi i : ℝ) t x := by
    rw [show c - n*x = ∑ i, ((xi i : ℝ) - |(xi i : ℝ)| - 2*t*Real.log 2 - x) by
      rw [Finset.sum_sub_distrib]
      simp [c, n]]
    exact Finset.sum_le_sum fun i _ => by linarith [level_lower_bound (xi i : ℝ) ht hx]
  have hsq : 0 ≤ (x-eta-a)^2 / (g : ℝ) := by positivity
  have he : (x-eta-a)^2 / (g : ℝ) =
      (x-eta)^2 / (g : ℝ) - n*x + n*eta + a^2/(g : ℝ) := by
    dsimp [a]
    field_simp
    ring
  rw [he] at hsq
  unfold meanFieldPotential
  linarith

/-- At an applied source, using the zero-source minimizer as a trial total
field gives a lower bound on the optimized free-energy drop. -/
theorem mean_field_source_drop [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (hg : 0 < g) {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hx : 0 ≤ x)
    (hm : IsMinOn (meanFieldPotential xi g t 0) (Ici 0) x) (eta : ℝ) :
    (2*eta*x - eta^2) / (g : ℝ) ≤
      meanFieldFreeEnergy xi g t 0 - meanFieldFreeEnergy xi g t eta := by
  have hmin : meanFieldFreeEnergy xi g t 0 = meanFieldPotential xi g t 0 x :=
    IsLeast.csInf_eq ⟨⟨x, hx, rfl⟩, fun _ ⟨_, hy, he⟩ => he ▸ hm hy⟩
  have htrial : meanFieldFreeEnergy xi g t eta ≤ meanFieldPotential xi g t eta x :=
    csInf_le (potential_bddBelow xi g hg ht eta) ⟨x, hx, rfl⟩
  calc
    _ = meanFieldPotential xi g t 0 x - meanFieldPotential xi g t eta x := by
      unfold meanFieldPotential
      ring
    _ ≤ _ := by rw [hmin]; exact sub_le_sub_left htrial _

end Grain.BCS

namespace Grain.CrystalBCS

open BCS Set

/-- For a constant Cooper channel, a positive minimum of the finite
quadratic free energy satisfies the band gap equation on every level. -/
theorem thermal_gap_of_minimum {s : Type} [Fintype s] [Nonempty s]
    (c : Crystal s) (b : BandData s) (g : ℚ) (hc : constantChannel c b g)
    (hxi : ∀ i, xi c b i ≠ 0) (hg : 0 < g) {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    IsMinOn (meanFieldPotential (xi c b) g t 0) (Ici 0) x ↔
      thermalGapEquation c b t (fun _ => x) :=
  (thermal_minimum_iff (xi c b) g hxi hg ht hx).trans
    (thermal_gap_equation c b g hc hx.ne').symm

end Grain.CrystalBCS
