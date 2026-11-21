import Grain.Energy
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.IntermediateValue

/-! Finite-band BCS with a constant attractive Cooper matrix. Temperature
is measured as k_B T in energy units. The chemical potential is fixed and
no sampled band level equals it. -/

namespace Grain.BCS

open Set

noncomputable def thermalFactor (x : ℝ) : ℝ :=
  (Real.exp x - 1) / (Real.exp x + 1)

noncomputable def quasiparticle (xi delta : ℝ) : ℝ :=
  Real.sqrt (xi ^ 2 + delta ^ 2)

noncomputable def criticalResponse [Fintype ι] (xi : ι → ℚ) (g : ℚ) (t : ℝ) : ℝ :=
  (g : ℝ) * ∑ i, thermalFactor (|(xi i : ℝ)| / t) / (2 * |(xi i : ℝ)|)

noncomputable def zeroResponse [Fintype ι] (xi : ι → ℚ) (g : ℚ) (delta : ℝ) : ℝ :=
  (g : ℝ) * ∑ i, 1 / (2 * quasiparticle (xi i : ℝ) delta)

/-- Squaring the BdG block gives the squared quasiparticle energy times
the identity. This is the same block used to compute the Fermi weights. -/
theorem bdg_squared (xi delta x y : ℝ) :
    xi * (xi * x + delta * y) + delta * (delta * x - xi * y) =
        quasiparticle xi delta ^ 2 * x ∧
    delta * (xi * x + delta * y) - xi * (delta * x - xi * y) =
        quasiparticle xi delta ^ 2 * y := by
  rw [quasiparticle, Real.sq_sqrt (by positivity)]
  constructor <;> ring

/-- The off-diagonal entry of the thermal occupation matrix of the
two-dimensional BdG block, with diagonal entries `xi` and `-xi`. -/
theorem anomalous_entry (E delta fPlus fMinus : ℝ) :
    fPlus * (delta / E / 2) + fMinus * (-delta / E / 2) =
      -delta * ((fMinus - fPlus) / (2 * E)) := by ring

/-- Opposite quasiparticle energies give the thermal factor in the
off-diagonal occupation when their Fermi weights are subtracted. -/
theorem fermi_difference (x : ℝ) :
    1 / (Real.exp (-x) + 1) - 1 / (Real.exp x + 1) = thermalFactor x := by
  rw [Real.exp_neg, thermalFactor]
  have hp := Real.exp_pos x
  field_simp
  ring

/-- The off-diagonal parts of the two spectral projections are
respectively `delta/(2E)` and `-delta/(2E)`. With Fermi occupations
the negative of the resulting entry is the pair amplitude. -/
theorem thermal_bdg_entry (xi delta t : ℝ) :
    let E := quasiparticle xi delta
    (1 / (Real.exp (E / t) + 1)) * (delta / E / 2) +
      (1 / (Real.exp (-(E / t)) + 1)) * (-delta / E / 2) =
      -delta * (thermalFactor (E / t) / (2 * E)) := by
  intro E
  rw [anomalous_entry, fermi_difference]

/-- Pair self-consistency with a constant Cooper matrix gives one scalar
equation. The same amplitude appears at every level. -/
theorem nonzero_constant_gap_iff [Fintype ι] (chi : ι → ℝ) (g delta : ℝ)
    (h : delta ≠ 0) :
    delta = g * (∑ i, delta * chi i) ↔ g * (∑ i, chi i) = 1 := by
  rw [← Finset.mul_sum]
  constructor <;> intro h' <;> apply (mul_right_inj' h).mp <;> nlinarith

/-- The constant vector is an eigenvector of the normal gap operator.
Every nonzero eigenvalue is its eigenvalue, because the operator's image
consists only of constant vectors. -/
theorem rank_one_growth {ι : Type} [Fintype ι] [Nonempty ι] (chi : ι → ℝ) (g : ℝ) :
    ∀ (growth : ℝ) (v : ι → ℝ), v ≠ 0 →
    (∀ i, g * (∑ j, chi j * v j) = growth * v i) →
    growth = 0 ∨ growth = g * ∑ j, chi j := by
  intro growth v hv he
  by_cases hz : growth = 0
  · exact Or.inl hz
  right
  let i := Classical.arbitrary ι
  have hconst (j : ι) : v j = v i :=
    (mul_right_inj' hz).1 ((he j).symm.trans (he i))
  have hvi : v i ≠ 0 := fun h => hv (funext fun j => (hconst j).trans h)
  have hi := he i
  simp only [hconst, ← Finset.sum_mul] at hi
  exact (mul_left_inj' hvi).1 (by linear_combination -hi)

theorem thermal_fraction_mono {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ y) :
    (x - 1) / (x + 1) ≤ (y - 1) / (y + 1) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

private theorem fraction_strict {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x < y) :
    (x - 1) / (x + 1) < (y - 1) / (y + 1) := by
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem quasiparticle_pos {xi : ℝ} (h : xi ≠ 0) (delta : ℝ) :
    0 < quasiparticle xi delta :=
  Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _))

section Response

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
private theorem level_pos (xi : ι → ℚ) (hxi : ∀ i, xi i ≠ 0) (i : ι) :
    0 < |(xi i : ℝ)| := abs_pos.mpr (by exact_mod_cast hxi i)

theorem critical_continuous (xi : ι → ℚ) (g : ℚ) :
    ContinuousOn (criticalResponse xi g) (Ioi 0) := by
  unfold criticalResponse
  apply continuousOn_const.mul
  apply continuousOn_finsetSum
  intro i _
  have hdiv : ContinuousOn (fun t : ℝ => |(xi i : ℝ)| / t) (Ioi 0) :=
    continuousOn_const.div continuousOn_id (fun _ ht => ne_of_gt ht)
  have he : ContinuousOn (fun t : ℝ => Real.exp (|(xi i : ℝ)| / t)) (Ioi 0) :=
    Real.continuous_exp.comp_continuousOn hdiv
  unfold thermalFactor
  exact ((he.sub continuousOn_const).div (he.add continuousOn_const)
    (fun t _ => ne_of_gt (add_pos_of_pos_of_nonneg (Real.exp_pos _) zero_le_one))).div_const _

theorem zero_continuous (xi : ι → ℚ) (g : ℚ) (hxi : ∀ i, xi i ≠ 0) :
    Continuous (zeroResponse xi g) := by
  unfold zeroResponse
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i _
  have he : Continuous (fun d : ℝ => quasiparticle (xi i : ℝ) d) := by
    unfold quasiparticle
    fun_prop
  exact continuous_const.div (continuous_const.mul he)
    (fun d => mul_ne_zero (by norm_num) (ne_of_gt (quasiparticle_pos (by exact_mod_cast hxi i) d)))

theorem critical_decreases [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) :
    StrictAntiOn (criticalResponse xi g) (Ioi 0) := by
  intro a ha b _ hab
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  unfold criticalResponse
  apply mul_lt_mul_of_pos_left _ hg'
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hp := level_pos xi hxi i
  apply div_lt_div_of_pos_right _ (by positivity)
  apply fraction_strict (Real.exp_nonneg _) (Real.exp_nonneg _)
  exact Real.exp_strictMono (div_lt_div_of_pos_left hp ha hab)

theorem zero_decreases [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) :
    StrictAntiOn (zeroResponse xi g) (Ici 0) := by
  intro a ha b _ hab
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  unfold zeroResponse
  apply mul_lt_mul_of_pos_left _ hg'
  apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
  intro i _
  have hne : (xi i : ℝ) ≠ 0 := by exact_mod_cast hxi i
  have hsq := pow_lt_pow_left₀ hab ha (by decide : 2 ≠ 0)
  have hE : quasiparticle (xi i : ℝ) a < quasiparticle (xi i : ℝ) b := by
    unfold quasiparticle
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith)
  exact one_div_lt_one_div_of_lt (by have := quasiparticle_pos hne a; positivity)
    (mul_lt_mul_of_pos_left hE (by norm_num))

private theorem unique_crossing {domain : Set ℝ} {f : ℝ → ℝ} {lo hi : ℝ}
    (hm : StrictAntiOn f domain) (hd : Icc lo hi ⊆ domain) (hord : lo ≤ hi)
    (hc : ContinuousOn f (Icc lo hi)) (hl : 1 ≤ f lo) (hu : f hi ≤ 1) :
    ∃ x ∈ Icc lo hi, f x = 1 ∧ ∀ y ∈ domain, f y = 1 → y = x := by
  obtain ⟨x, hx, he⟩ := intermediate_value_Icc' hord hc ⟨hu, hl⟩
  exact ⟨x, hx, he, fun y hy hey => hm.injOn hy (hd hx) (hey.trans he.symm)⟩

theorem critical_bracket [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {lo hi : ℝ} (hlo : 0 < lo)
    (hord : lo ≤ hi) (hl : 1 ≤ criticalResponse xi g lo)
    (hu : criticalResponse xi g hi ≤ 1) :
    ∃ t ∈ Icc lo hi, criticalResponse xi g t = 1 ∧
      (∀ T > 0, criticalResponse xi g T = 1 → T = t) ∧
      (∀ T > 0, 1 < criticalResponse xi g T ↔ T < t) := by
  have hd : Icc lo hi ⊆ Ioi 0 := fun _ hx => hlo.trans_le hx.1
  have hm := critical_decreases xi g hxi hg
  obtain ⟨t, ht, he, huniq⟩ :=
    unique_crossing hm hd hord ((critical_continuous xi g).mono hd) hl hu
  refine ⟨t, ht, he, huniq, fun T hT => ?_⟩
  rw [← he]
  exact ⟨fun h => lt_of_not_ge fun hn => (not_lt_of_ge (hm.antitoneOn (hd ht) hT hn)) h,
    fun h => hm hT (hd ht) h⟩

theorem gap_bracket [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (hg : 0 < g) {lo hi : ℝ} (hlo : 0 < lo)
    (hord : lo ≤ hi) (hl : 1 ≤ zeroResponse xi g lo)
    (hu : zeroResponse xi g hi ≤ 1) :
    ∃ delta ∈ Icc lo hi, zeroResponse xi g delta = 1 ∧
      ∀ x ≥ 0, zeroResponse xi g x = 1 → x = delta :=
  unique_crossing (zero_decreases xi g hxi hg) (fun _ hx => hlo.le.trans hx.1)
    hord (zero_continuous xi g hxi).continuousOn hl hu

def normalLimit (xi : ι → ℚ) (g : ℚ) : ℚ :=
  g * ∑ i, 1 / (2 * |xi i|)

theorem normal_limit_eq (xi : ι → ℚ) (g : ℚ) :
    (normalLimit xi g : ℝ) = zeroResponse xi g 0 := by
  simp [normalLimit, zeroResponse, quasiparticle, Real.sqrt_sq_eq_abs]

/-- A subcritical static channel has neither a positive-temperature
linear instability nor a positive zero-temperature gap. -/
theorem subcritical [Nonempty ι] (xi : ι → ℚ) (g : ℚ)
    (hxi : ∀ i, xi i ≠ 0) (h : normalLimit xi g ≤ 1) :
    (∀ t > 0, criticalResponse xi g t < 1) ∧
    (∀ d > 0, zeroResponse xi g d < 1) := by
  have hf {x : ℝ} (hx : 0 ≤ x) : 0 ≤ thermalFactor x := by
    unfold thermalFactor
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)) (by positivity)
  by_cases hg : 0 < g
  · have hg' : (0 : ℝ) < g := by exact_mod_cast hg
    have h₀ : zeroResponse xi g 0 ≤ 1 := by
      rw [← normal_limit_eq]
      exact_mod_cast h
    refine ⟨fun t ht => ?_, fun d hd => (zero_decreases xi g hxi hg
      (show 0 ∈ Ici (0 : ℝ) by simp) hd.le hd).trans_le h₀⟩
    apply lt_of_lt_of_le _ h₀
    simp only [criticalResponse, zeroResponse, quasiparticle, zero_pow (by decide : 2 ≠ 0),
      add_zero, Real.sqrt_sq_eq_abs]
    apply mul_lt_mul_of_pos_left _ hg'
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    apply div_lt_div_of_pos_right _ (by have := level_pos xi hxi i; positivity)
    unfold thermalFactor
    exact (div_lt_one (by positivity)).2 (by linarith)
  · have hg' : (g : ℝ) ≤ 0 := by exact_mod_cast le_of_not_gt hg
    refine ⟨fun t ht => lt_of_le_of_lt ?_ zero_lt_one, fun d _ => lt_of_le_of_lt ?_ zero_lt_one⟩
    · unfold criticalResponse
      exact mul_nonpos_of_nonpos_of_nonneg hg' (Finset.sum_nonneg fun i _ =>
        div_nonneg (hf (by positivity)) (by positivity))
    · unfold zeroResponse quasiparticle
      exact mul_nonpos_of_nonpos_of_nonneg hg' (Finset.sum_nonneg fun i _ => by positivity)

noncomputable def minimumExcitation (xi : ι → ℚ) (delta : ℝ) : ℝ :=
  sInf (range fun i => quasiparticle (xi i : ℝ) delta)

omit [Fintype ι] in
theorem minimum_excitation_eq (xi : ι → ℚ) (delta : ℝ) (k : ι)
    (hm : ∀ i, |xi k| ≤ |xi i|) :
    minimumExcitation xi delta = quasiparticle (xi k : ℝ) delta := by
  apply IsLeast.csInf_eq
  refine ⟨⟨k, rfl⟩, ?_⟩
  rintro _ ⟨i, rfl⟩
  have ha : |(xi k : ℝ)| ≤ |(xi i : ℝ)| := by exact_mod_cast hm i
  have hs := pow_le_pow_left₀ (abs_nonneg _) ha 2
  simp only [sq_abs] at hs
  exact Real.sqrt_le_sqrt (by linarith)

theorem excitation_bracket (xi deltaLo deltaHi lo hi : ℚ) {delta : ℝ}
    (hdl : (deltaLo : ℝ) ≤ delta) (hdu : delta ≤ (deltaHi : ℝ))
    (hd : 0 ≤ deltaLo) (hlo : 0 ≤ lo ∧ lo^2 ≤ xi^2 + deltaLo^2)
    (hhi : 0 ≤ hi ∧ xi^2 + deltaHi^2 ≤ hi^2) :
    (lo : ℝ) ≤ quasiparticle (xi : ℝ) delta ∧
      quasiparticle (xi : ℝ) delta ≤ (hi : ℝ) := by
  have he : (0 : ℝ) ≤ deltaLo := by exact_mod_cast hd
  have hs := pow_le_pow_left₀ he hdl 2
  have ht := pow_le_pow_left₀ (he.trans hdl) hdu 2
  have hl : (lo : ℝ)^2 ≤ (xi : ℝ)^2 + (deltaLo : ℝ)^2 := by exact_mod_cast hlo.2
  have hu : (xi : ℝ)^2 + (deltaHi : ℝ)^2 ≤ (hi : ℝ)^2 := by exact_mod_cast hhi.2
  unfold quasiparticle
  exact ⟨Real.le_sqrt_of_sq_le (by linarith),
    Real.sqrt_le_iff.mpr ⟨by exact_mod_cast hhi.1, by linarith⟩⟩

end Response

end Grain.BCS
