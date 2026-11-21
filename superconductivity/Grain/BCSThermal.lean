import Grain.BCSCertificate
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Positive-temperature gap response of the finite constant Cooper channel. -/

namespace Grain.BCS

open Set

private theorem exp_difference_gt {x : ℝ} (hx : 0 < x) :
    2 * x < Real.exp x - Real.exp (-x) := by
  let f := fun z : ℝ => Real.exp z - Real.exp (-z) - 2 * z
  have hf : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _) (by dsimp [f]; fun_prop)
    intro z hz
    have hz' : 0 < z := by simpa only [interior_Ici, mem_Ioi] using hz
    have hn := (Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
    have hd := ((Real.hasDerivAt_exp z).sub hn).sub ((hasDerivAt_id z).const_mul 2)
    have hd' : deriv f z = Real.exp z - Real.exp (-z) * (-1) - 2 * 1 := hd.deriv
    rw [hd']
    have hExp : 1 < Real.exp z := by simpa using Real.exp_strictMono hz'
    have hprod : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have hs := sq_pos_of_ne_zero (sub_ne_zero.mpr hExp.ne')
    apply (mul_pos_iff_of_pos_right (Real.exp_pos z)).mp
    nlinarith only [hprod, hs]
  have ht := hf (a := 0) (by simp) hx.le hx
  norm_num [f] at ht
  linarith

/-- The ratio tanh(x/2)/x is strictly decreasing for positive x. -/
theorem thermal_ratio_decreases : StrictAntiOn (fun x : ℝ => thermalFactor x / x) (Ioi 0) := by
  have hcts : ContinuousOn thermalFactor (Ioi 0) := by
    unfold thermalFactor
    exact Real.continuous_exp.continuousOn.sub continuousOn_const |>.div
      (Real.continuous_exp.continuousOn.add continuousOn_const) (fun _ _ => by positivity)
  apply strictAntiOn_of_deriv_neg (convex_Ioi _) (hcts.div continuousOn_id fun _ hx => hx.ne')
  intro x hx
  have hp : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
  have he := Real.hasDerivAt_exp x
  have hq := ((he.sub_const 1).div (he.add_const 1) (by positivity)).div
    (hasDerivAt_id x) hp.ne'
  have hex := Real.exp_pos x
  have hprod : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hdiff := mul_lt_mul_of_pos_right (exp_difference_gt hp) hex
  have hpden : Real.exp x + 1 ≠ 0 := by positivity
  have hd : deriv (fun y => thermalFactor y / y) x =
      (2 * x * Real.exp x - (Real.exp x ^ 2 - 1)) / ((Real.exp x + 1)^2 * x^2) := by
    calc
      _ = _ := hq.deriv
      _ = _ := by
        dsimp
        field_simp
        ring
  change deriv (fun y => thermalFactor y / y) x < 0
  rw [hd]
  exact div_neg_of_neg_of_pos (by nlinarith only [hdiff, hprod]) (by positivity)

noncomputable def thermalSusceptibility (e t : ℝ) : ℝ := thermalFactor (e / t) / (2 * e)

theorem susceptibility_decreases {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (fun e => thermalSusceptibility e t) (Ioi 0) := by
  intro a ha b hb hab
  have hscale {e : ℝ} (he : 0 < e) :
      thermalSusceptibility e t = (thermalFactor (e / t) / (e / t)) / (2 * t) := by
    unfold thermalSusceptibility
    field_simp
  change thermalSusceptibility b t < thermalSusceptibility a t
  rw [hscale ha, hscale hb]
  exact div_lt_div_of_pos_right
    (thermal_ratio_decreases (div_pos ha ht) (div_pos hb ht) (div_lt_div_of_pos_right hab ht))
    (by positivity)

noncomputable def thermalResponse [Fintype ι] (xi : ι → ℚ) (g : ℚ) (t delta : ℝ) : ℝ :=
  (g : ℝ) * ∑ i, thermalSusceptibility (quasiparticle (xi i : ℝ) delta) t

theorem thermal_response_zero [Fintype ι] (xi : ι → ℚ) (g : ℚ) (t : ℝ) :
    thermalResponse xi g t 0 = criticalResponse xi g t := by
  simp [thermalResponse, quasiparticle, Real.sqrt_sq_eq_abs, thermalSusceptibility, criticalResponse]

theorem thermal_continuous [Fintype ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (t : ℝ) : Continuous (thermalResponse xi g t) := by
  have hp (i : ι) (d : ℝ) : 0 < quasiparticle (xi i : ℝ) d :=
    quasiparticle_pos (by exact_mod_cast hxi i) d
  unfold thermalResponse
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  have hq : Continuous (fun d : ℝ => quasiparticle (xi i : ℝ) d) := by
    unfold quasiparticle
    fun_prop
  have he : Continuous (fun d : ℝ => Real.exp (quasiparticle (xi i : ℝ) d / t)) :=
    Real.continuous_exp.comp (hq.div_const _)
  unfold thermalSusceptibility thermalFactor
  exact ((he.sub continuous_const).div (he.add continuous_const)
    (fun d => ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos _) zero_le_one))).div (continuous_const.mul hq)
      (fun d => ne_of_gt (mul_pos (by norm_num) (hp i d)))

theorem thermal_decreases [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t : ℝ} (ht : 0 < t) :
    StrictAntiOn (thermalResponse xi g t) (Ici 0) := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  intro a ha b _ hab
  unfold thermalResponse
  apply mul_lt_mul_of_pos_left _ hg'
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hp (d : ℝ) : 0 < quasiparticle (xi i : ℝ) d :=
    quasiparticle_pos (by exact_mod_cast hxi i) d
  apply susceptibility_decreases ht (hp a) (hp b)
  unfold quasiparticle
  have hs := pow_lt_pow_left₀ hab ha (by decide : 2 ≠ 0)
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

theorem thermal_bracket [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t lo hi : ℝ} (ht : 0 < t) (hlo : 0 ≤ lo)
    (hord : lo ≤ hi) (hl : 1 ≤ thermalResponse xi g t lo) (hu : thermalResponse xi g t hi ≤ 1) :
    ∃ d ∈ Icc lo hi, thermalResponse xi g t d = 1 ∧
      ∀ x ≥ 0, thermalResponse xi g t x = 1 → x = d := by
  obtain ⟨d, hd, he⟩ :=
    intermediate_value_Icc' hord (thermal_continuous xi g hxi t).continuousOn ⟨hu, hl⟩
  have hmono := thermal_decreases xi g hxi hg ht
  exact ⟨d, hd, he, fun x hx hx' => hmono.injOn hx (hlo.trans hd.1) (hx'.trans he.symm)⟩

theorem no_thermal_gap [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) {t : ℝ} (ht : 0 < t)
    (h : criticalResponse xi g t ≤ 1) :
    ∀ d > 0, thermalResponse xi g t d < 1 := by
  intro d hd
  by_cases hg : 0 < g
  · have he := thermal_decreases xi g hxi hg ht (show 0 ∈ Ici (0 : ℝ) by simp) hd.le hd
    rw [thermal_response_zero] at he
    exact he.trans_le h
  · unfold thermalResponse
    refine (mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_gt hg) ?_).trans_lt zero_lt_one
    apply Finset.sum_nonneg
    intro i _
    unfold thermalSusceptibility thermalFactor
    have hp : 0 ≤ quasiparticle (xi i : ℝ) d / t := by unfold quasiparticle; positivity
    exact div_nonneg (div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hp)) (by positivity))
      (by unfold quasiparticle; positivity)

/-- The finite constant channel has a positive gap exactly when the
normal-state thermal response exceeds one. -/
theorem positive_gap_iff [Fintype ι] [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {t : ℝ} (ht : 0 < t) :
    (∃ d > 0, thermalResponse xi g t d = 1) ↔ 1 < criticalResponse xi g t := by
  constructor
  · rintro ⟨d, hd, he⟩
    exact lt_of_not_ge fun h => (no_thermal_gap xi g hxi ht h d hd).ne he
  · intro he
    let a : ℝ := (g : ℝ) * Fintype.card ι
    let hi := a + 1
    have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hhi : 0 < hi := by dsimp [hi]; linarith
    have hupper : thermalResponse xi g t hi < 1 := by
      calc
        thermalResponse xi g t hi ≤ (g : ℝ) * ∑ _ : ι, 1 / (2 * hi) := by
          apply mul_le_mul_of_nonneg_left _ hg'.le
          apply Finset.sum_le_sum
          intro i _
          let E := quasiparticle (xi i : ℝ) hi
          have hE : hi ≤ E := by
            change hi ≤ Real.sqrt ((xi i : ℝ)^2 + hi^2)
            exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))
          have hdiv : 0 < 2 * E := mul_pos (by norm_num) (hhi.trans_le hE)
          have hf : thermalFactor (E / t) ≤ 1 := by
            unfold thermalFactor
            exact (div_le_one (by positivity)).2 (by linarith)
          exact (div_le_div_of_nonneg_right hf hdiv.le).trans
            (one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_left hE zero_le_two))
        _ = a / (2 * hi) := by simp [a, div_eq_mul_inv, mul_assoc]
        _ < 1 := (div_lt_one (by positivity)).2 (by dsimp [hi]; linarith)
    have h0 : 1 < thermalResponse xi g t 0 := by simpa only [thermal_response_zero] using he
    obtain ⟨d, hd, hd', _⟩ := thermal_bracket xi g hxi hg ht le_rfl hhi.le h0.le hupper.le
    refine ⟨d, lt_of_le_of_ne hd.1 ?_, hd'⟩
    intro hz
    rw [← hz] at hd'
    linarith

/-- Bounding each quasiparticle energy gives a response enclosure with
the same rational thermal evaluator as the normal state. -/
theorem thermal_enclosure [Fintype ι] (xi : ι → ℚ) (g t delta : ℚ) (lo hi : ι → ℚ)
    (hg : 0 ≤ g) (ht : 0 < t) (h : ∀ i, energyTest (xi i) delta (lo i) (hi i)) :
    criticalResponse hi g t ≤ thermalResponse xi g t delta ∧
      thermalResponse xi g t delta ≤ criticalResponse lo g t := by
  have hg' : (0 : ℝ) ≤ g := by exact_mod_cast hg
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hlo (i : ι) : 0 < (lo i : ℝ) := by exact_mod_cast (h i).1
  have he (i : ι) := energy_enclosure _ _ _ _ (h i)
  have hp (i : ι) := (hlo i).trans_le (he i).1
  have hhi (i : ι) := (hp i).trans_le (he i).2
  constructor <;> unfold criticalResponse thermalResponse <;>
    apply mul_le_mul_of_nonneg_left _ hg' <;> apply Finset.sum_le_sum
  · intro i _
    rw [abs_of_pos (hhi i)]
    exact (susceptibility_decreases ht').antitoneOn (hp i) (hhi i) (he i).2
  · intro i _
    rw [abs_of_pos (hlo i)]
    exact (susceptibility_decreases ht').antitoneOn (hlo i) (hp i) (he i).1

end Grain.BCS

namespace Grain.CrystalBCS

open Grain.BCS

def thermalGapEquation [Fintype s] (c : Crystal s) (b : BandData s) (t : ℝ) (gap : s → ℝ) : Prop :=
  ∀ i, gap i = ∑ j, (cooperKernel c b i j : ℝ) *
    (gap j * thermalSusceptibility (quasiparticle (xi c b j : ℝ) (gap j)) t)

theorem thermal_gap_equation [Fintype s] [Nonempty s] (c : Crystal s) (b : BandData s)
    (g : ℚ) (hc : constantChannel c b g) {t delta : ℝ} (hd : delta ≠ 0) :
    thermalGapEquation c b t (fun _ => delta) ↔ thermalResponse (xi c b) g t delta = 1 := by
  let chi (j : s) := thermalSusceptibility (quasiparticle (xi c b j : ℝ) delta) t
  have hk (i j : s) : cooperKernel c b i j = g := hc i j
  have hsum (i : s) : (∑ j, (cooperKernel c b i j : ℝ) * (delta * chi j)) =
      (g : ℝ) * ∑ j, delta * chi j := by simp only [hk, Finset.mul_sum]
  change (∀ i, delta = ∑ j, (cooperKernel c b i j : ℝ) * (delta * chi j)) ↔ _
  simp only [hsum, nonzero_constant_gap_iff _ _ _ hd, thermalResponse, chi]
  exact ⟨fun h => h (Classical.arbitrary s), fun h _ => h⟩

end Grain.CrystalBCS
