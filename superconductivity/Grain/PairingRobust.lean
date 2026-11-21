import Grain.PairingMaterial

/-! Variational transfer of a rational pencil certificate to every
real pencil in an entrywise envelope. The rational reference can
include a block of discarded frequencies with zero pairing kernel. -/

namespace Grain.Pairing.Material

section Robust

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def realForm (A : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * (x i * x j)

noncomputable def realMetric (d : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, d i * x i ^ 2

noncomputable def values (A : ι → ι → ℝ) (d : ι → ℝ) : Set ℝ :=
  {q | ∃ x, 0 < realMetric d x ∧ q = realForm A x / realMetric d x}

noncomputable def spectrumTop (A : ι → ι → ℝ) (d : ι → ℝ) : ℝ :=
  sSup (values A d)

def radiusRow (B : ι → ι → Interval) (A : ι → ι → ℚ) (i : ι) : ℚ :=
  ∑ j, ((B i j).radius (A i j) + (B j i).radius (A j i)) / 2

def upperKernel (A : ι → ι → ℚ) (error : ι → ℚ) (i j : ι) : ℚ :=
  A i j + if i = j then error i else 0

def metricEndpoint (E : ι → Interval) (u : ℚ) (i : ι) : ℚ :=
  if 0 ≤ u then (E i).lo else (E i).hi

def trialEnergyLower (B : ι → ι → Interval) (x : ι → ℚ) : ℚ :=
  ∑ i, ∑ j, (if 0 ≤ x i * x j then (B i j).lo else (B i j).hi) * (x i * x j)

def trialTest (B : ι → ι → Interval) (E : ι → Interval) (lo : ℚ) (x : ι → ℚ) : Prop :=
  0 < rationalMetricForm (fun i => (E i).lo) x ∧
  lo * rationalMetricForm (fun i => if 0 ≤ lo then (E i).hi else (E i).lo) x ≤ trialEnergyLower B x

instance (B : ι → ι → Interval) (E : ι → Interval) (lo : ℚ) (x : ι → ℚ) :
    Decidable (trialTest B E lo x) := by unfold trialTest; infer_instance

omit [DecidableEq ι] in
theorem trial_enclosure (B : ι → ι → Interval) (E : ι → Interval) (lo : ℚ) (x : ι → ℚ)
    (F : ι → ι → ℝ) (D : ι → ℝ) (hF : ∀ i j, (B i j).contains (F i j))
    (hD : ∀ i, (E i).contains (D i)) (h : trialTest B E lo x) :
    let y := fun i => (x i : ℝ)
    0 < realMetric D y ∧ (lo : ℝ) * realMetric D y ≤ realForm F y := by
  let y := fun i => (x i : ℝ)
  have hm1 : (rationalMetricForm (fun i => (E i).lo) x : ℝ) ≤ realMetric D y := by
    unfold rationalMetricForm realMetric y
    push_cast
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i).1 (sq_nonneg _)
  have hm2 : realMetric D y ≤ (rationalMetricForm (fun i => (E i).hi) x : ℝ) := by
    unfold rationalMetricForm realMetric y
    push_cast
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hD i).2 (sq_nonneg _)
  have hf : (trialEnergyLower B x : ℝ) ≤ realForm F y := by
    unfold trialEnergyLower realForm y
    push_cast
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hs : 0 ≤ x i * x j
    · simpa [hs] using mul_le_mul_of_nonneg_right (hF i j).1
        (by exact_mod_cast hs : 0 ≤ (x i : ℝ) * (x j : ℝ))
    · simpa [hs] using mul_le_mul_of_nonpos_right (hF i j).2
        (by exact_mod_cast (le_of_not_ge hs) : (x i : ℝ) * (x j : ℝ) ≤ 0)
  refine ⟨(by exact_mod_cast h.1 : (0 : ℝ) < (rationalMetricForm (fun i => (E i).lo) x : ℝ)).trans_le hm1, ?_⟩
  have hq := h.2
  by_cases hs : 0 ≤ lo
  · simp only [ite_eq_left hs] at hq
    exact (mul_le_mul_of_nonneg_left hm2 (by exact_mod_cast hs)).trans
      ((by exact_mod_cast hq : (lo : ℝ) * (rationalMetricForm (fun i => (E i).hi) x : ℝ) ≤
        (trialEnergyLower B x : ℝ)).trans hf)
  · simp only [ite_eq_right hs] at hq
    exact (mul_le_mul_of_nonpos_left hm1 (by exact_mod_cast le_of_not_ge hs)).trans
      ((by exact_mod_cast hq : (lo : ℝ) * (rationalMetricForm (fun i => (E i).lo) x : ℝ) ≤
        (trialEnergyLower B x : ℝ)).trans hf)

omit [DecidableEq ι] in
theorem form_enclosure (B : ι → ι → Interval) (A : ι → ι → ℚ)
    (F : ι → ι → ℝ) (hF : ∀ i j, (B i j).contains (F i j))
    (d : ι → ℚ) (bound : ℚ) (hrow : ∀ i, radiusRow B A i ≤ bound * d i)
    (x : ι → ℝ) :
    |realForm F x - form A x| ≤ (bound : ℝ) * metricForm d x := by
  let R (i j : ι) : ℝ := ((B i j).radius (A i j) : ℚ)
  let diff (i j : ι) := (F i j - (A i j : ℝ)) * (x i * x j)
  have hD : realForm F x - form A x = ∑ i, ∑ j, diff i j := by
    simp only [realForm, form, ← Finset.sum_sub_distrib, ← sub_mul, diff]
  have hterm (i j : ι) : |diff i j| ≤ R i j * ((x i)^2 + (x j)^2) / 2 := by
    have ht := Interval.abs_sub_le_radius (hF i j) (A i j)
    have hn := (abs_nonneg _).trans ht
    dsimp only [diff]
    rw [abs_mul]
    calc
      _ ≤ R i j * |x i * x j| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      _ ≤ _ := by
        rw [mul_div_assoc, abs_mul]
        apply mul_le_mul_of_nonneg_left _ hn
        nlinarith only [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
  have he : (∑ i, ∑ j, R i j * ((x i)^2 + (x j)^2) / 2) =
      ∑ i, (radiusRow B A i : ℝ) * (x i)^2 := by
    have split (i j : ι) :
        R i j * ((x i)^2 + (x j)^2) / 2 =
          R i j / 2 * (x i)^2 + R i j / 2 * (x j)^2 := by ring
    simp only [split, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => R i j / 2 * (x j)^2), ← Finset.sum_add_distrib]
    unfold radiusRow
    push_cast
    simp only [Finset.sum_mul, add_div, add_mul, Finset.sum_add_distrib, R]
  rw [hD]
  calc
    _ ≤ ∑ i, ∑ j, |diff i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, R i j * ((x i)^2 + (x j)^2) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := he
    _ ≤ _ := by
      unfold metricForm
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hr : (radiusRow B A i : ℝ) ≤ (bound : ℝ) * (d i : ℝ) := by exact_mod_cast hrow i
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hr (sq_nonneg (x i))

omit [DecidableEq ι] in
theorem metric_shift (E : ι → Interval) (D : ι → ℝ) (u : ℚ)
    (hD : ∀ i, (E i).contains (D i)) (x : ι → ℝ) :
    (u : ℝ) * metricForm (metricEndpoint E u) x ≤ (u : ℝ) * realMetric D x := by
  unfold metricForm realMetric
  simp only [Finset.mul_sum, ← mul_assoc]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  by_cases h : 0 ≤ u
  · simp only [metricEndpoint, ite_eq_left h]
    exact mul_le_mul_of_nonneg_left (hD i).1 (by exact_mod_cast h)
  · simp only [metricEndpoint, ite_eq_right h]
    exact mul_le_mul_of_nonpos_left (hD i).2 (by exact_mod_cast le_of_not_ge h)

/-- The padded reference solve proves a two-sided bound for all pencils
in the envelope. No eigensolve on the whole realized frequency grid is
needed for this theorem. -/
theorem spectrum_enclosure (B : ι → ι → Interval) (E : ι → Interval)
    (A : ι → ι → ℚ) (error : ι → ℚ) (lo hi : ℚ)
    (trial : ι → ℚ) (L : ι → ι → ℚ) (pivots : ι → ℚ)
    (hl : trialTest B E lo trial)
    (hu : upperTest (upperKernel A error) (metricEndpoint E hi) hi L pivots)
    (hr : ∀ i, radiusRow B A i ≤ error i)
    (F : ι → ι → ℝ) (D : ι → ℝ)
    (hF : ∀ i j, (B i j).contains (F i j)) (hD : ∀ i, (E i).contains (D i)) :
    (lo : ℝ) ≤ spectrumTop F D ∧ spectrumTop F D ≤ (hi : ℝ) := by
  let y : ι → ℝ := fun i => (trial i : ℝ)
  have hc := trial_enclosure B E lo trial F D hF hD hl
  have trialVal : realForm F y / realMetric D y ∈ values F D := ⟨y, hc.1, rfl⟩
  have hupper (x : ι → ℝ) : realForm F x ≤ (hi : ℝ) * realMetric D x := by
    have hf := (abs_le.1 (form_enclosure B A F hF error 1 (by simpa using hr) x)).2
    norm_num at hf
    have he : form (upperKernel A error) x = form A x + metricForm error x := by
      unfold upperKernel form metricForm
      simp only [Rat.cast_add, add_mul, Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp [apply_ite (fun q : ℚ => (q : ℝ)), ite_mul, pow_two]
    calc
      realForm F x ≤ form (upperKernel A error) x := by linarith only [hf, he]
      _ ≤ (hi : ℝ) * metricForm (metricEndpoint E hi) x := pencil_upper _ _ hi L pivots hu x
      _ ≤ _ := metric_shift E D hi hD x
  have hbound : ∀ q ∈ values F D, q ≤ (hi : ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (div_le_iff₀ hx).2 (hupper x)
  have hlower : (lo : ℝ) ≤ realForm F y / realMetric D y := (le_div_iff₀ hc.1).2 hc.2
  exact ⟨hlower.trans (le_csSup ⟨_, hbound⟩ trialVal), csSup_le ⟨_, trialVal⟩ hbound⟩

end Robust

def referenceKernel (b : Mesh p) (retained cutoff : ℕ) (t : ℚ) (a d : p × Fin N) : ℚ :=
  if a.2.val < retained ∧ d.2.val < retained then (kernelBox b cutoff t a d).mid else 0

theorem material_spectrum_enclosure {p : Type} [Fintype p] [DecidableEq p]
    (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (t : ℚ) (retained cutoff : ℕ) (lo hi : ℚ) (error : p × Fin N → ℚ)
    (trial : p × Fin N → ℚ) (L : (p × Fin N) → (p × Fin N) → ℚ) (pivots : p × Fin N → ℚ)
    (hl : trialTest (kernelBox b cutoff t) (metricBox b t) lo trial)
    (hu : upperTest (upperKernel (referenceKernel b retained cutoff t) error)
      (metricEndpoint (metricBox b t) hi) hi L pivots)
    (he : ∀ i, radiusRow (kernelBox b cutoff t) (referenceKernel b retained cutoff t) i ≤ error i) :
    (lo : ℝ) ≤ spectrumTop (meshKernel r cutoff t) (meshMetric b r t : p × Fin N → ℝ) ∧
      spectrumTop (meshKernel r cutoff t) (meshMetric b r t : p × Fin N → ℝ) ≤ (hi : ℝ) :=
  spectrum_enclosure _ _ _ error lo hi trial L pivots hl hu he _ _
    (kernel_enclosure b r h cutoff t) (metric_enclosure b r h hw hd t)

end Grain.Pairing.Material
