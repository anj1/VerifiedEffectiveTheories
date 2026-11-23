import Grain.PairingClosure
import Grain.PairingFullExample
import Mathlib.Analysis.Real.Pi.Bounds

/-! Compare the uncut exchange and the finite-band normal term with the
actual rational margins of the all-frequency certificate. -/

namespace Grain.Pairing.Material.AllFrequencyCertificate

open Finset

private def row0 : Grid := (0, 0)
private def row2 : Grid := (0, 2)

private def coldMargin : ℚ := 2169939/2000000 - 1
private def hotMargin : ℚ := 1 - 9760019/10000000

private theorem dos_lo (r : Realization Patch) (h : mesh.matches r) (j : Patch) :
    ((dosBox mesh j).lo : ℝ) ≤ dos mesh r j :=
  (dos_enclosure mesh r h (by decide) j).1

private theorem metric_le (r : Realization Patch) (h : mesh.matches r)
    (t : ℚ) (a : Grid) {U : ℚ} (hu : (frequencyMetricBox mesh t a).hi ≤ U) :
    frequencyMetric mesh r t a ≤ U :=
  (frequency_metric_enclosure mesh r h (by decide) (by decide +kernel) t a).2.trans
    (by exact_mod_cast hu)

private theorem coulomb_lower (r : Realization Patch) (h : mesh.matches r) :
    (1299/10 : ℝ) ≤ r.coulomb 0 0 := by
  convert (h.2.2 0 0).2.1 using 1
  change (1299/10 : ℝ) = ((1299/10 : ℚ) : ℝ)
  norm_num

/-- Even on the three-frequency grid the row error from an instantaneous
screened interaction exceeds both of the advertised endpoint allowances.
This holds for every normal diagonal used in the comparison. -/
theorem screening_exceeds_endpoint_rows (r : Realization Patch) (h : mesh.matches r)
    (t ε : ℚ) (he : (t = tau0 ∧ ε = coldMargin) ∨ (t = tau1 ∧ ε = hotMargin))
    (D : Grid → ℝ) :
    (ε : ℝ) * frequencyMetric mesh r t row0 <
      (∑ q, |meshKernel r 3 t row0 q - meshKernel r 2 t row0 q|) +
      |D row0 - frequencyMetric mesh r t row0| := by
  have hr := instantaneous_row_lower r (cutoff := 2) (t : ℝ) row0 row2 (by decide)
  have hc := (coulomb_lower r h).trans (le_abs_self _)
  change 2 * |r.coulomb 0 0| ≤ _ at hr
  have hlow : (2598/10 : ℝ) ≤
      ∑ q, |meshKernel r 3 t row0 q - meshKernel r 2 t row0 q| := by linarith
  have hb : (ε : ℝ) * frequencyMetric mesh r t row0 < 2598/10 := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hm := metric_le r h tau0 row0 (U := 2300) (by decide +kernel)
      norm_num [coldMargin] at *
      linarith only [hm]
    · have hm := metric_le r h tau1 row0 (U := 2300) (by decide +kernel)
      norm_num [hotMargin] at *
      linarith only [hm]
  exact hb.trans_le (hlow.trans (le_add_of_nonneg_right (abs_nonneg _)))

private def twoEntries (s : ℝ) (a : Grid) : ℝ :=
  if a = row0 then 1 else if a = row2 then s else 0

private theorem two_entries_form (F : Grid → Grid → ℝ) (D : Grid → ℝ) (s : ℝ) :
    realForm F (twoEntries s) - realMetric D (twoEntries s) =
    F row0 row0 - D row0 + (F row0 row2 + F row2 row0) * s +
      (F row2 row2 - D row2) * s^2 := by
  norm_num [twoEntries, row0, row2, realForm, realMetric,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

/-- At the hot endpoint even a direct quadratic-form bound with a 5%
allowance fails, independently of the normal diagonal. The two trials
with opposite relative signs isolate the off-diagonal error. -/
theorem hot_screening_exceeds_form_budget (r : Realization Patch) (h : mesh.matches r)
    (D : Grid → ℝ) :
    ∃ x : Grid → ℝ,
      (1/20 : ℝ) * realMetric (frequencyMetric mesh r tau1) x <
        |(realForm (meshKernel r 3 tau1) x - realMetric D x) -
          (realForm (meshKernel r 2 tau1) x - realMetric (frequencyMetric mesh r tau1) x)| := by
  by_contra! hbound
  have hp := hbound (twoEntries 1)
  have hn := hbound (twoEntries (-1))
  let E := frequencyMetric mesh r tau1 (N := 3)
  have hmetric (s : ℝ) : realMetric E (twoEntries s) = E row0 + E row2 * s^2 := by
    norm_num [twoEntries, row0, row2, realMetric,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
  have h02 := instantaneous_cutoff_error r 2 tau1 row0 row2 (by decide)
  have h20 := instantaneous_cutoff_error r 2 tau1 row2 row0 (by decide)
  change _ = -2 * r.coulomb 0 0 at h02 h20
  change _ ≤ (1/20 : ℝ) * realMetric E (twoEntries 1) at hp
  change _ ≤ (1/20 : ℝ) * realMetric E (twoEntries (-1)) at hn
  rw [two_entries_form, two_entries_form, hmetric] at hp hn
  have hm0 : E row0 ≤ 2300 := by
    apply metric_le r h tau1 row0 (U := 2300)
    decide +kernel
  have hm2 : E row2 ≤ 6500 := by
    apply metric_le r h tau1 row2 (U := 6500)
    decide +kernel
  have hc := coulomb_lower r h
  have hl := (abs_le.mp hp).1
  have hu := (abs_le.mp hn).2
  norm_num only [one_pow, neg_sq, mul_one, mul_neg, Rat.cast_ofNat] at hl hu
  linarith only [hl, hu, h02, h20, hm0, hm2, hc]

private theorem hot_radial_le (r : Realization Patch) (h : mesh.matches r)
    (hs : ∀ j, sampled (mesh.bands j) (r.bands j)) (j : Patch) (k : ℕ) :
    finiteBandNormal (mesh.bands j) (r.bands j) ((2 * (k : ℝ) + 1) * tau1) ≤
      dos mesh r j / 3 := by
  have ht : (12 : ℝ) ≤ (2 * (k : ℝ) + 1) * tau1 := by
    norm_num [tau1]
  have hd : 0 < Real.pi * ((2 * (k : ℝ) + 1) * tau1) := by positivity
  have hp : (36 : ℝ) ≤ Real.pi * ((2 * (k : ℝ) + 1) * tau1) := by
    have hh := mul_le_mul Real.pi_gt_three.le ht (by norm_num : (0 : ℝ) ≤ 12) Real.pi_pos.le
    norm_num at hh
    exact hh
  apply (finite_band_normal_bounds (hs j)
    ((by norm_num : (0 : ℝ) < 12).trans_le ht)).2.trans
  apply (div_le_iff₀ hd).2
  have hw := dos_lo r h j
  have hwpos : 0 ≤ dos mesh r j := by
    have hh : ∀ i : Patch, 0 ≤ (dosBox mesh i).lo := by decide +kernel
    exact (by exact_mod_cast hh j : 0 ≤ ((dosBox mesh j).lo : ℝ)).trans hw
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hp (by positivity))
  have hmass : ∀ j : Patch, bandMass (mesh.bands j) ≤ 12 * (dosBox mesh j).lo := by
    decide +kernel
  have hmass' : (bandMass (mesh.bands j) : ℝ) ≤ 12 * ((dosBox mesh j).lo : ℝ) := by
    exact_mod_cast hmass j
  linarith only [hmass', hw]

/-- At the hot endpoint the finite-band contribution to the one-phonon
normal numerator is at most one third of the flat-DOS contribution.
The resulting diagonal error is at least 37.5% of the reference metric
on patch zero at the first positive frequency. -/
theorem hot_finite_band_normal_error (r : Realization Patch) (h : mesh.matches r)
    (hs : ∀ j, sampled (mesh.bands j) (r.bands j)) :
    (3/8 : ℝ) * fullMetric mesh r tau1 (0, 0) ≤
      fullMetric mesh r tau1 (0, 0) - finiteBandNormalMetricZero mesh r tau1 0 := by
  let A := ∑ j, dos mesh r j * profile (r.modes 0 j) tau1 0
  have ha (j : Patch) : 0 ≤ dos mesh r j := by
    have hh : ∀ i : Patch, 0 ≤ (dosBox mesh i).lo := by decide +kernel
    exact (by exact_mod_cast hh j : 0 ≤ ((dosBox mesh j).lo : ℝ)).trans (dos_lo r h j)
  have hd : (3/2500 : ℝ) ≤ dos mesh r 0 := by
    have hq : (3/2500 : ℚ) ≤ (dosBox mesh 0).lo := by decide +kernel
    have hh : ((3/2500 : ℚ) : ℝ) ≤ ((dosBox mesh 0).lo : ℝ) := Rat.cast_le.mpr hq
    norm_num at hh
    exact hh.trans (dos_lo r h 0)
  have hp : (1200 : ℝ) ≤ profile (r.modes 0 0) tau1 0 := by
    have hq : (1200 : ℚ) ≤ (profileBox mesh 0 0 tau1 0).lo := by decide +kernel
    exact (by exact_mod_cast hq : (1200 : ℝ) ≤ _).trans
      (profile_enclosure mesh r h 0 0 tau1 0).1
  have hA : (36/25 : ℝ) ≤ A :=
    (show (36/25 : ℝ) = (3/2500) * 1200 by norm_num).le.trans
      ((mul_le_mul hd hp (by norm_num) (ha 0)).trans (single_le_sum
        (f := fun j => dos mesh r j * profile (r.modes 0 j) tau1 0)
        (fun j _ => mul_nonneg (ha j) (profile_bounds _ _ (h.2.1 0 j) tau1 0).1)
        (mem_univ 0)))
  have hsum : (∑ j, ∑' k, finiteBandNormalTerm mesh r tau1 0 j k) ≤ A / 3 := by
    unfold A
    simp only [sum_div]
    refine sum_le_sum fun j _ => ?_
    have ht : (0 : ℝ) < (tau1 : ℝ) := by norm_num [tau1]
    rw [show dos mesh r j * profile (r.modes 0 j) tau1 0 / 3 =
      (dos mesh r j / 3) * profile (r.modes 0 j) tau1 0 by ring]
    exact (finite_band_normal_sum mesh r h hs ht 0 j (hot_radial_le r h hs j)).2
  have he : fullMetric mesh r tau1 (0, 0) = (1 + A) / dos mesh r 0 := by
    simp [fullMetric, A]
  rw [he, finiteBandNormalMetricZero, ← sub_div, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (ha 0)
  linarith only [hA, hsum]

end Grain.Pairing.Material.AllFrequencyCertificate
