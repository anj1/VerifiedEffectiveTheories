import Grain.CrystalBCS

/-! Rational bounds used by the finite-band BCS solver. Lean checks the
endpoint signs using Taylor enclosures and squared comparisons. -/

namespace Grain.BCS

def expTaylor (x : ℚ) (terms : ℕ) : ℚ :=
  ∑ k ∈ Finset.range terms, x^k / (k.factorial : ℚ)

def expRemainder (x : ℚ) (terms : ℕ) : ℚ :=
  x^terms * (terms + 1 : ℚ) / ((terms.factorial : ℚ) * terms)

def expLower (x : ℚ) (terms scale : ℕ) : ℚ :=
  expTaylor (x / scale) terms ^ scale

def expUpper (x : ℚ) (terms scale : ℕ) : ℚ :=
  (expTaylor (x / scale) terms + expRemainder (x / scale) terms) ^ scale

theorem exp_enclosure (x : ℚ) (terms scale : ℕ) (hx : 0 ≤ x)
    (hterms : 0 < terms) (hs : 0 < scale) (hxs : x ≤ scale) :
    0 ≤ expLower x terms scale ∧
    (expLower x terms scale : ℝ) ≤ Real.exp x ∧
    Real.exp x ≤ (expUpper x terms scale : ℝ) := by
  let y : ℝ := (x : ℝ) / (scale : ℝ)
  have hn : 0 < (scale : ℝ) := by exact_mod_cast hs
  have hy : 0 ≤ y := div_nonneg (by exact_mod_cast hx) hn.le
  have h1 : y ≤ 1 := (div_le_iff₀ hn).2 (by
    rw [one_mul]
    exact_mod_cast hxs)
  have hp : (scale : ℝ) * y = (x : ℝ) := by
    dsimp [y]
    field_simp
  have he : Real.exp (x : ℝ) = Real.exp y ^ scale := by
    rw [← Real.exp_nat_mul, hp]
  have hs0 : 0 ≤ expTaylor (x / (scale : ℚ)) terms := by
    apply Finset.sum_nonneg
    intro k _
    positivity
  have hs1 : 0 ≤ ∑ k ∈ Finset.range terms, y^k / (k.factorial : ℝ) := by
    exact Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨pow_nonneg hs0 _, ?_, ?_⟩
  · rw [he]
    simp only [expLower, expTaylor, Rat.cast_pow, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
    exact pow_le_pow_left₀ hs1 (Real.sum_le_exp_of_nonneg hy terms) _
  · rw [he]
    simp only [expUpper, expTaylor, expRemainder, Rat.cast_pow, Rat.cast_sum, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_one]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_bound' hy h1 hterms) _

def thermalFraction (x : ℚ) : ℚ := (x - 1) / (x + 1)

def fermiLower (x : ℚ) (terms scale : ℕ) : ℚ :=
  thermalFraction (if x ≤ 32 then expLower x terms scale else
    max (expLower 32 terms 32) (expTaylor x terms))

def fermiUpper (x : ℚ) (terms scale : ℕ) : ℚ :=
  if x ≤ 32 then thermalFraction (expUpper x terms scale) else 1

private theorem fermi_enclosure (x : ℚ) (terms scale : ℕ) (hx : 0 ≤ x)
    (hn : 0 < terms) (hs : 0 < scale) (hscale : x ≤ 32 → x ≤ scale) :
    (fermiLower x terms scale : ℝ) ≤ thermalFactor (x : ℝ) ∧
    thermalFactor (x : ℝ) ≤ (fermiUpper x terms scale : ℝ) := by
  by_cases h : x ≤ 32
  · obtain ⟨hl, hm, hu⟩ := exp_enclosure x terms scale hx hn hs (hscale h)
    have hn' : (0 : ℝ) ≤ (expLower x terms scale : ℝ) := by exact_mod_cast hl
    simp only [fermiLower, fermiUpper, h, ite_true, thermalFraction, thermalFactor]
    push_cast
    exact ⟨thermal_fraction_mono hn' (Real.exp_nonneg _) hm,
      thermal_fraction_mono (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hu) hu⟩
  · obtain ⟨hl, hm, _⟩ := exp_enclosure 32 terms 32 (by norm_num) hn (by decide) (by norm_num)
    have hx' : (32 : ℝ) ≤ x := by exact_mod_cast (le_of_not_ge h)
    have h0 : (0 : ℝ) ≤ (expLower 32 terms 32 : ℝ) := by exact_mod_cast hl
    have h1 : (expLower 32 terms 32 : ℝ) ≤ Real.exp (x : ℝ) :=
      hm.trans (Real.exp_le_exp_of_le hx')
    have h2 : (expTaylor x terms : ℝ) ≤ Real.exp (x : ℝ) := by
      simpa only [expTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using
        Real.sum_le_exp_of_nonneg (by exact_mod_cast hx : (0 : ℝ) ≤ x) terms
    simp only [fermiLower, fermiUpper, h, ite_false, thermalFactor, thermalFraction]
    push_cast
    refine ⟨thermal_fraction_mono (h0.trans (le_max_left _ _)) (Real.exp_nonneg _)
      (max_le h1 h2), ?_⟩
    exact (div_le_one (by positivity)).2 (by linarith)

def criticalLower [Fintype ι] (xi : ι → ℚ) (g t : ℚ) (terms : ℕ) (scale : ι → ℕ) : ℚ :=
  g * ∑ i, fermiLower (|xi i| / t) terms (scale i) / (2 * |xi i|)

def criticalUpper [Fintype ι] (xi : ι → ℚ) (g t : ℚ) (terms : ℕ) (scale : ι → ℕ) : ℚ :=
  g * ∑ i, fermiUpper (|xi i| / t) terms (scale i) / (2 * |xi i|)

theorem critical_enclosure [Fintype ι] (xi : ι → ℚ) (g t : ℚ) (terms : ℕ) (scale : ι → ℕ)
    (hg : 0 ≤ g) (ht : 0 < t) (hterms : 0 < terms)
    (hs : ∀ i, 0 < scale i ∧ (|xi i| / t ≤ 32 → |xi i| / t ≤ scale i)) :
    (criticalLower xi g t terms scale : ℝ) ≤ criticalResponse xi g (t : ℝ) ∧
    criticalResponse xi g (t : ℝ) ≤ (criticalUpper xi g t terms scale : ℝ) := by
  have hg' : (0 : ℝ) ≤ g := by exact_mod_cast hg
  have hat (i : ι) := fermi_enclosure (|xi i| / t) terms (scale i) (by positivity)
    hterms (hs i).1 (hs i).2
  simp only [Rat.cast_div, Rat.cast_abs] at hat
  constructor
  · unfold criticalLower criticalResponse
    push_cast
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (hat i).1 (by positivity)) hg'
  · unfold criticalUpper criticalResponse
    push_cast
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      div_le_div_of_nonneg_right (hat i).2 (by positivity)) hg'

def zeroAt [Fintype ι] (energies : ι → ℚ) (g : ℚ) : ℚ :=
  g * ∑ i, 1 / (2 * energies i)

def energyTest (xi delta lo hi : ℚ) : Prop :=
  0 < lo ∧ 0 ≤ hi ∧ lo^2 ≤ xi^2 + delta^2 ∧ xi^2 + delta^2 ≤ hi^2

instance (xi delta lo hi : ℚ) : Decidable (energyTest xi delta lo hi) := by
  unfold energyTest
  infer_instance

theorem energy_enclosure (xi delta lo hi : ℚ) (h : energyTest xi delta lo hi) :
    (lo : ℝ) ≤ quasiparticle (xi : ℝ) (delta : ℝ) ∧
    quasiparticle (xi : ℝ) (delta : ℝ) ≤ (hi : ℝ) := by
  unfold quasiparticle
  exact ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast h.2.2.1),
    Real.sqrt_le_iff.mpr ⟨by exact_mod_cast h.2.1, by exact_mod_cast h.2.2.2⟩⟩

theorem zero_enclosure [Fintype ι] (xi : ι → ℚ) (g delta : ℚ) (lo hi : ι → ℚ)
    (hg : 0 ≤ g) (h : ∀ i, energyTest (xi i) delta (lo i) (hi i)) :
    (zeroAt hi g : ℝ) ≤ zeroResponse xi g (delta : ℝ) ∧
    zeroResponse xi g (delta : ℝ) ≤ (zeroAt lo g : ℝ) := by
  have hg' : (0 : ℝ) ≤ g := by exact_mod_cast hg
  have hlo (i : ι) : 0 < (lo i : ℝ) := by exact_mod_cast (h i).1
  have he (i : ι) := energy_enclosure _ _ _ _ (h i)
  simp only [zeroAt, zeroResponse, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat]
  constructor <;> apply mul_le_mul_of_nonneg_left _ hg' <;> apply Finset.sum_le_sum
  · intro i _
    exact one_div_le_one_div_of_le (by have := (hlo i).trans_le (he i).1; positivity)
      (by linarith [(he i).2])
  · intro i _
    exact one_div_le_one_div_of_le (mul_pos (by norm_num) (hlo i)) (by linarith [(he i).1])

end Grain.BCS
