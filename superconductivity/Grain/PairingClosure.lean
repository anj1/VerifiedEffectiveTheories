import Grain.PairingParent
import Grain.PairingFrequency

/-! Two terms in the comparison with a time-local screened parent can be
computed before estimating any higher-order many-body corrections. -/

namespace Grain.Pairing.Material

open Finset

variable {p : Type} [Fintype p] {N : ℕ}

/-- Time-local screening evaluated on even relative-frequency pair fields.
In the folded convention each column has two equal frequency contributions.
The equal-time field samples the sum over all retained relative frequencies. -/
noncomputable def instantaneousScreeningForm (C : p → p → ℝ) (x : p × Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, (-2 * C i j) * (∑ n, x (i, n)) * (∑ m, x (j, m))

theorem instantaneous_screening_form (C : p → p → ℝ) (x : p × Fin N → ℝ) :
    instantaneousScreeningForm C x = realForm (fun a b => -2 * C a.1 b.1) x := by
  simp only [instantaneousScreeningForm, realForm, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_assoc, sum_mul_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]

/-- The tree-level Cooper exchange computed from the parent force,
deformation and screened operator, before a Matsubara-support reduction. -/
noncomputable def parentExchange (d : HarmonicBand.Input n c m) (t : ℝ)
    (a b : HarmonicBand.Orbital n × Fin N) : ℝ :=
  (∑ k : Fin m, (HarmonicBand.modeEntry d k a.1 b.1 : ℝ)^2 /
    (d.force k + (realTransferSq t a.2 b.2).1)) +
  (∑ k : Fin m, (HarmonicBand.modeEntry d k a.1 b.1 : ℝ)^2 /
    (d.force k + (realTransferSq t a.2 b.2).2)) - 2 * parentCoulomb d a.1 b.1

theorem parent_exchange_eq_mesh (d : HarmonicBand.Input n c m) (h : HarmonicBand.Valid d)
    (μ t : ℝ) (a b : HarmonicBand.Orbital n × Fin N) :
    parentExchange d t a b = meshKernel (parentRealization d μ) N t a b := by
  simp only [parentExchange, meshKernel, a.2.isLt, b.2.isLt, and_self, ite_true, parent_phonon d h]
  rfl

/-- For a finite band orbital, the radial factor is the signed imaginary
part of its bare Matsubara propagator with energy relative to μ. -/
theorem bare_normal_propagator (ω ξ : ℝ) :
    -((ω * Complex.I - (ξ : ℂ))⁻¹ : ℂ).im = ω / (ω^2 + ξ^2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  ring_nf

omit [Fintype p] in
/-- On any column beyond the cutoff the retarded term cancels in the
comparison. This identity also holds with row and column interchanged. -/
theorem instantaneous_cutoff_error (r : Realization p) (cutoff : ℕ) (t : ℝ)
    (a b : p × Fin N) (h : ¬ (a.2.val < cutoff ∧ b.2.val < cutoff)) :
    meshKernel r N t a b - meshKernel r cutoff t a b = -2 * r.coulomb a.1 b.1 := by
  simp [meshKernel, a.2.isLt, b.2.isLt, h]

/-- The omitted column alone is a lower bound on the absolute row error.
Any correction to the diagonal metric adds a nonnegative amount to this
budget. -/
theorem instantaneous_row_lower (r : Realization p) {cutoff : ℕ} (t : ℝ)
    (a b : p × Fin N) (hb : cutoff ≤ b.2.val) :
    2 * |r.coulomb a.1 b.1| ≤
      ∑ q, |meshKernel r N t a q - meshKernel r cutoff t a q| := by
  classical
  have h := single_le_sum
    (f := fun q => |meshKernel r N t a q - meshKernel r cutoff t a q|)
    (fun q (_ : q ∈ univ) => abs_nonneg _) (mem_univ b)
  rwa [instantaneous_cutoff_error r cutoff t a b (by omega), neg_mul, abs_neg, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h

/-- Enlarging the grid at fixed Coulomb support adds a nondecaying
contribution in each omitted column of the same patch. -/
theorem instantaneous_tail_row_lower (r : Realization p) (cutoff tail : ℕ) (t : ℝ)
    (a : p × Fin (cutoff + tail)) (j : p) :
    (tail : ℝ) * (2 * |r.coulomb a.1 j|) ≤
      ∑ q, |meshKernel r (cutoff + tail) t a q - meshKernel r cutoff t a q| := by
  let col : Fin tail ↪ p × Fin (cutoff + tail) :=
    ⟨fun k => (j, Fin.natAdd cutoff k), fun k l h => by
      apply Fin.ext
      have he := congrArg (fun a : p × Fin (cutoff + tail) => a.2.val) h
      simpa [Fin.val_natAdd] using he⟩
  let err (q : p × Fin (cutoff + tail)) :=
    |meshKernel r (cutoff + tail) t a q - meshKernel r cutoff t a q|
  have h (k : Fin tail) : err (col k) = 2 * |r.coulomb a.1 j| := by
    have hk : cutoff ≤ (col k).2.val := Nat.le_add_right _ _
    unfold err
    rw [instantaneous_cutoff_error r cutoff t a (col k) (by omega), neg_mul, abs_neg, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rfl
  calc
    _ = ∑ k : Fin tail, err (col k) := by simp [h, nsmul_eq_mul]
    _ = ∑ q ∈ univ.map col, err q := (sum_map _ _ _).symm
    _ ≤ ∑ q, err q := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)

/-- In the actual harmonic parent the same difference is exactly the
projected time-local screened matrix element. -/
theorem parent_exchange_cutoff_error (d : HarmonicBand.Input n c m) (h : HarmonicBand.Valid d)
    (μ t : ℝ) (cutoff : ℕ) (a b : HarmonicBand.Orbital n × Fin N)
    (hb : cutoff ≤ b.2.val) :
    parentExchange d t a b - meshKernel (parentRealization d μ) cutoff t a b =
      -2 * parentCoulomb d a.1 b.1 := by
  rw [parent_exchange_eq_mesh d h μ]
  exact instantaneous_cutoff_error _ _ _ _ _ (by omega)

/-- An electronic interaction invisible to the two same-orbital pair
matrix elements. It changes the energy of a split pair. -/
def addSplitPairDensity (d : HarmonicBand.Input 2 c m) (u : ℚ) : HarmonicBand.Input 2 c m :=
  { d with density := ⟨(0, 0), (1, 1), u⟩ :: d.density }

theorem add_split_pair_density_valid (d : HarmonicBand.Input 2 c m)
    (h : HarmonicBand.Valid d) (u : ℚ) : HarmonicBand.Valid (addSplitPairDensity d u) := by
  rcases h with ⟨hn, hs, hd, hc, hf, ho, hsc⟩
  exact ⟨hn, hs, by simpa [addSplitPairDensity] using hd, hc, hf, ho, hsc⟩

theorem add_split_pair_density_projection (d : HarmonicBand.Input 2 c m)
    (u : ℚ) (i j : Fin 2) : parentCoulomb (addSplitPairDensity d u) i j = parentCoulomb d i j := by
  have hocc : ∀ k : Fin 2, (HarmonicBand.occupied (pairState k) (0, 0) &&
      HarmonicBand.occupied (pairState k) (1, 1)) = false := by decide +kernel
  unfold parentCoulomb HarmonicBand.screened
  simp only [addSplitPairDensity, HarmonicBand.scatteringColumn, List.filter_cons,
    hocc, Bool.false_eq_true, ite_false]

theorem add_split_pair_density_entry (d : HarmonicBand.Input 2 c m) (u : ℚ) :
    HarmonicBand.screened (addSplitPairDensity d u) 9 9 =
      HarmonicBand.screened d 9 9 + u := by
  have hocc : (HarmonicBand.occupied (9 : HarmonicBand.State 2) (0, 0) &&
      HarmonicBand.occupied (9 : HarmonicBand.State 2) (1, 1)) = true := by decide +kernel
  simp only [HarmonicBand.screened, addSplitPairDensity, HarmonicBand.scatteringColumn, ite_true,
    List.filter_cons, hocc, List.map_cons, List.sum_cons]
  ring

/-- Electronic spectral mass and levels for a finite band. This is the
discrete spectral measure before a flat-DOS replacement. -/
def bandMass (samples : List Sample) : ℚ := (samples.map Sample.weight).sum

/-- Positive-frequency imaginary part of the bare normal propagator,
integrated over the band and divided by π, in the convention of the metric. -/
noncomputable def finiteBandNormal (samples : List Sample) (levels : List ℝ) (ω : ℝ) : ℝ :=
  ((samples.zipWith (fun s ξ => (s.weight : ℝ) * (ω / (ω^2 + ξ^2))) levels).sum) / Real.pi

theorem finite_band_normal_bounds {samples : List Sample} {levels : List ℝ}
    (h : sampled samples levels) {ω : ℝ} (hω : 0 < ω) :
    0 ≤ finiteBandNormal samples levels ω ∧ finiteBandNormal samples levels ω ≤
      (bandMass samples : ℝ) / (Real.pi * ω) := by
  unfold finiteBandNormal
  rw [mul_comm Real.pi ω, ← div_div]
  have hh : 0 ≤ (samples.zipWith (fun s ξ => (s.weight : ℝ) * (ω / (ω^2 + ξ^2))) levels).sum ∧
      (samples.zipWith (fun s ξ => (s.weight : ℝ) * (ω / (ω^2 + ξ^2))) levels).sum ≤
        (bandMass samples : ℝ) / ω := by
    induction h with
    | nil => simp [bandMass]
    | @cons s ξ ss ξs hs _ ih =>
      have hw : (0 : ℝ) ≤ s.weight := by exact_mod_cast hs.1
      simp only [List.zipWith_cons_cons, List.sum_cons, bandMass, List.map_cons,
        Rat.cast_add, add_div] at *
      refine ⟨add_nonneg (mul_nonneg hw (by positivity)) ih.1, add_le_add ?_ ih.2⟩
      rw [← mul_one_div]
      apply mul_le_mul_of_nonneg_left _ hw
      rw [← div_eq_mul_one_div]
      rw [← one_div ω]
      apply (div_le_div_iff₀ (by positivity) hω).2
      nlinarith only [sq_nonneg ξ]
  exact ⟨div_nonneg hh.1 Real.pi_pos.le, div_le_div_of_nonneg_right hh.2 Real.pi_pos.le⟩

/-- At external frequency zero in the positive-frequency numbering, the
folded one-phonon line has a nonnegative coefficient at each internal
frequency. This term keeps the finite electronic spectral measure. -/
noncomputable def finiteBandNormalTerm (b : Mesh p) (r : Realization p)
    (t : ℝ) (i j : p) (k : ℕ) : ℝ :=
  finiteBandNormal (b.bands j) (r.bands j) ((2 * (k : ℝ) + 1) * t) *
    (profile (r.modes i j) t k - profile (r.modes i j) t (k + 1))

omit [Fintype p] in
/-- The two internal frequencies have opposite imaginary parts. The
positive partner uses the difference transfer, and the negative partner
uses the sum transfer. -/
theorem finite_band_normal_fold_zero (b : Mesh p) (r : Realization p)
    (t : ℝ) (i j : p) (n k : Fin N) (hn : n.val = 0) :
    finiteBandNormalTerm b r t i j k.val =
      finiteBandNormal (b.bands j) (r.bands j) ((2 * (k.val : ℝ) + 1) * t) *
      (phononResponse (r.modes i j) (realTransferSq t n k).1 -
        phononResponse (r.modes i j) (realTransferSq t n k).2) := by
  have hf := transfer_profile (r.modes i j) t n k
  rw [hf.1, hf.2]
  simp [finiteBandNormalTerm, separation, hn]

noncomputable def finiteBandNormalMetricZero (b : Mesh p) (r : Realization p)
    (t : ℝ) (i : p) : ℝ :=
  (1 + ∑ j, ∑' k, finiteBandNormalTerm b r t i j k) / dos b r i

omit [Fintype p] in
private theorem profile_step_nonneg (b : Mesh p) (r : Realization p) (h : b.matches r)
    (t : ℝ) (i j : p) (k : ℕ) :
    0 ≤ profile (r.modes i j) t k - profile (r.modes i j) t (k + 1) := by
  apply sub_nonneg.mpr
  unfold profile
  apply phonon_decreases _ _ (sq_nonneg _) ?_ (h.2.1 i j)
  push_cast
  nlinarith only [sq_nonneg t, mul_nonneg (sq_nonneg t) (Nat.cast_nonneg (α := ℝ) k)]

omit [Fintype p] in
/-- A uniform bound on the radial weight controls the convergent normal
sum. At external index zero the flat-DOS sum telescopes to the zero-transfer
phonon response. -/
theorem finite_band_normal_sum (b : Mesh p) (r : Realization p) (h : b.matches r)
    (hs : ∀ j, sampled (b.bands j) (r.bands j)) {t : ℝ} (ht : 0 < t)
    (i j : p) {B : ℝ} (hB : ∀ k : ℕ,
      finiteBandNormal (b.bands j) (r.bands j) ((2 * (k : ℝ) + 1) * t) ≤ B) :
    Summable (finiteBandNormalTerm b r t i j) ∧
      (∑' k, finiteBandNormalTerm b r t i j k) ≤ B * profile (r.modes i j) t 0 := by
  let f := profile (r.modes i j) t
  have hpos (k : ℕ) : 0 ≤ finiteBandNormalTerm b r t i j k :=
    mul_nonneg (finite_band_normal_bounds (hs j) (by positivity)).1
      (profile_step_nonneg b r h t i j k)
  have hBn := (finite_band_normal_bounds (hs j) (by positivity :
    0 < (2 * ((0 : ℕ) : ℝ) + 1) * t)).1.trans (hB 0)
  have hpartial (L : ℕ) : ∑ k ∈ range L, finiteBandNormalTerm b r t i j k ≤ B * f 0 := by
    calc
      _ ≤ ∑ k ∈ range L, B * (f k - f (k + 1)) := sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_right (hB k) (profile_step_nonneg b r h t i j k)
      _ = B * (f 0 - f L) := by rw [← mul_sum, sum_range_sub']
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sub_le_self _ (profile_bounds _ _ (h.2.1 i j) t L).1) hBn
  exact ⟨summable_of_sum_range_le hpos hpartial, Real.tsum_le_of_sum_range_le hpos hpartial⟩

end Grain.Pairing.Material
