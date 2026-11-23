import Grain.PairingRobust
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-! A threshold bracket covers a crossing of each fixed realization.
The Coulomb cutoff is a fixed set of frequency indices throughout a
bracket, so the pencil depends continuously on temperature. -/

namespace Grain.Pairing.Material

open Set

section Rayleigh

variable {ι : Type} [Fintype ι]

private def sphere : Set (ι → ℝ) := {x | normSq x = 1}

private theorem norm_continuous : Continuous (normSq (ι := ι)) := by
  unfold normSq
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).pow _

private theorem sphere_compact : IsCompact (sphere (ι := ι)) := by
  have hb : IsCompact (univ.pi fun _ : ι => Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hb.of_isClosed_subset ((isClosed_singleton (x := (1 : ℝ))).preimage norm_continuous)
  intro x hx
  rw [mem_univ_pi]
  intro i
  have hi : (x i)^2 ≤ normSq x := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  change normSq x = 1 at hx
  rw [hx] at hi
  exact ⟨by nlinarith, by nlinarith⟩

private theorem realMetric_pos {x : ι → ℝ} (hx : x ≠ 0) {D : ι → ℝ} (hD : ∀ i, 0 < D i) :
    0 < realMetric D x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact (mul_pos (hD i) (sq_pos_of_ne_zero hi)).trans_le
    (Finset.single_le_sum (fun j _ => mul_nonneg (hD j).le (sq_nonneg _)) (Finset.mem_univ i))

private theorem sphere_not_zero (x : ι → ℝ) (hx : x ∈ sphere) : x ≠ 0 := by
  intro he
  simp [sphere, normSq, he] at hx

private theorem rayleigh_homogeneous (F : ι → ι → ℝ) (D : ι → ℝ) (x : ι → ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    realForm F (fun i => c * x i) / realMetric D (fun i => c * x i) =
      realForm F x / realMetric D x := by
  have hf : realForm F (fun i => c * x i) = c^2 * realForm F x := by
    unfold realForm
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hd : realMetric D (fun i => c * x i) = c^2 * realMetric D x := by
    unfold realMetric
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hf, hd, mul_div_mul_left _ _ (pow_ne_zero _ hc)]

private theorem sphere_values (F : ι → ι → ℝ) (D : ι → ℝ) (hD : ∀ i, 0 < D i) :
    values F D = (fun x => realForm F x / realMetric D x) '' sphere := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hne : x ≠ 0 := by
      intro hz
      simp [realMetric, hz] at hx
    have hn : 0 < normSq x := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    let c := (Real.sqrt (normSq x))⁻¹
    have hc : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hn).ne'
    refine ⟨fun i => c * x i, ?_, rayleigh_homogeneous F D x hc⟩
    have hnrm : normSq (fun i => c * x i) = c^2 * normSq x := by
      unfold normSq
      simp only [mul_pow, Finset.mul_sum]
    change normSq (fun i => c * x i) = 1
    rw [hnrm]
    simp [c, inv_pow, Real.sq_sqrt hn.le, hn.ne']
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, realMetric_pos (sphere_not_zero x hx) hD, rfl⟩

theorem form_le_spectrum (F : ι → ι → ℝ) (D : ι → ℝ) (hD : ∀ i, 0 < D i)
    (x : ι → ℝ) : realForm F x ≤ spectrumTop F D * realMetric D x := by
  by_cases h : x = 0
  · simp [h, realForm, realMetric]
  · have hx := realMetric_pos h hD
    have hc : IsCompact (values F D) := by
      rw [sphere_values F D hD]
      apply sphere_compact.image_of_continuousOn
      apply ContinuousOn.div
      · exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
          continuous_const.mul ((continuous_apply i).mul (continuous_apply j))).continuousOn
      · exact (continuous_finsetSum _ fun i _ =>
          continuous_const.mul ((continuous_apply i).pow 2)).continuousOn
      · exact fun y hy => (realMetric_pos (sphere_not_zero y hy) hD).ne'
    exact (div_le_iff₀ hx).1 (le_csSup hc.bddAbove ⟨x, hx, rfl⟩)

theorem spectrum_continuous (F : ℝ → ι → ι → ℝ) (D : ℝ → ι → ℝ)
    (hF : ∀ i j, Continuous fun t => F t i j) (hD : ∀ i, Continuous fun t => D t i)
    (hp : ∀ t i, 0 < D t i) : Continuous fun t => spectrumTop (F t) (D t) := by
  let K := sphere (ι := ι)
  let : CompactSpace K := isCompact_iff_compactSpace.mp sphere_compact
  let f (t : ℝ) (x : K) := realForm (F t) x.val / realMetric (D t) x.val
  have hx (i : ι) : Continuous fun z : ℝ × K => z.2.val i :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hf : Continuous (Function.uncurry f) := by
    apply Continuous.div
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        ((hF i j).comp continuous_fst).mul ((hx i).mul (hx j))
    · exact continuous_finsetSum _ fun i _ => ((hD i).comp continuous_fst).mul ((hx i).pow 2)
    · intro z
      exact (realMetric_pos (sphere_not_zero z.2.val z.2.property) (hp z.1)).ne'
  have hs := (isCompact_univ (X := K)).continuous_sSup (f := f) hf
  have eq (t : ℝ) : values (F t) (D t) = f t '' univ := by
    rw [sphere_values _ _ (hp t)]
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
    · rintro ⟨x, _, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
  simpa only [spectrumTop, eq] using hs

open Matrix
open scoped Matrix in
/-- The top Rayleigh value is an eigenvalue of the symmetric generalized
pencil. Compactness gives a maximizer and a zero of its positive
semidefinite shifted form lies in the shifted kernel. -/
theorem spectrum_eigenvector [Nonempty ι] [DecidableEq ι] (F : ι → ι → ℝ) (D : ι → ℝ)
    (hs : ∀ i j, F i j = F j i) (hp : ∀ i, 0 < D i) :
    ∃ x : ι → ℝ, x ≠ 0 ∧ ∀ i,
      (∑ j, F i j * x j) = spectrumTop F D * D i * x i := by
  let f (x : ι → ℝ) := realForm F x / realMetric D x
  have hf : ContinuousOn f sphere := by
    apply ContinuousOn.div
    · exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply i).mul (continuous_apply j))).continuousOn
    · exact (continuous_finsetSum _ fun i _ =>
        continuous_const.mul ((continuous_apply i).pow 2)).continuousOn
    · exact fun x hx => (realMetric_pos (sphere_not_zero x hx) hp).ne'
  have hnon : (sphere (ι := ι)).Nonempty := by
    refine ⟨Pi.single (Classical.arbitrary ι) 1, ?_⟩
    simp [sphere, normSq, Pi.single_apply, ite_pow]
  have hgreat : IsGreatest (values F D) (spectrumTop F D) := by
    unfold spectrumTop
    rw [sphere_values F D hp]
    exact (sphere_compact.image_of_continuousOn hf).isGreatest_sSup (hnon.image f)
  obtain ⟨x, hx, hmax⟩ := hgreat.1
  have hne : x ≠ 0 := by intro he; simp [realMetric, he] at hx
  let M : Matrix ι ι ℝ := Matrix.of fun i j =>
    (if i = j then spectrumTop F D * D i else 0) - F i j
  have hform (y : ι → ℝ) : star y ⬝ᵥ (M *ᵥ y) =
      spectrumTop F D * realMetric D y - realForm F y := by
    have he : star y ⬝ᵥ (M *ᵥ y) = realForm (fun i j => M i j) y := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, realForm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [he]
    simp only [M, Matrix.of_apply, realForm, realMetric, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [ite_mul, mul_assoc, pow_two]
  have hM : M.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian.ext_iff]
      intro i j
      by_cases he : i = j
      · subst j
        simp
      · simp [M, he, Ne.symm he, hs j i]
    · intro y
      rw [hform]
      by_cases he : y = 0
      · simp [he, realMetric, realForm]
      · have hm := realMetric_pos he hp
        have hz := hgreat.2 (show f y ∈ values F D from ⟨y, hm, rfl⟩)
        exact sub_nonneg.mpr ((div_le_iff₀ hm).mp hz)
  have hzero : star x ⬝ᵥ (M *ᵥ x) = 0 := by
    rw [hform, (eq_div_iff hx.ne').mp hmax, sub_self]
  have hnull := hM.dotProduct_mulVec_zero_iff.mp hzero
  refine ⟨x, hne, fun i => ?_⟩
  have hz := congrFun hnull i
  simp [M, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul] at hz
  exact (sub_eq_zero.mp hz).symm

end Rayleigh

theorem continuous_phonon (b : List ModeBox) (m : List RealMode)
    (h : List.Forall₂ ModeBox.matches b m) (v : ℝ → ℝ) (hv : Continuous v)
    (hn : ∀ t, 0 ≤ v t) : Continuous fun t => phononResponse m (v t) := by
  induction h with
  | nil => exact continuous_const
  | @cons b m _ _ hb _ ih =>
    apply Continuous.add _ ih
    have ho : 0 < m.energy := (by exact_mod_cast hb.1 : (0 : ℝ) < b.energy.lo).trans_le hb.2.2.1.1
    exact continuous_const.div (continuous_const.add hv) (fun t =>
      ne_of_gt (add_pos_of_pos_of_nonneg (mul_pos ho ho) (hn t)))

theorem continuous_transfers (n m : Fin N) :
    (Continuous fun t => (realTransferSq t n m).1) ∧
    (Continuous fun t => (realTransferSq t n m).2) := by
  unfold realTransferSq
  exact ⟨(continuous_id.mul continuous_const).pow _, (continuous_id.mul continuous_const).pow _⟩

theorem mesh_metric_pos {p : Type} [Fintype p] (b : Mesh p) (r : Realization p)
    (h : b.matches r) (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (t : ℝ) (a : p × Fin N) : 0 < meshMetric b r t a := by
  have hwgt (i : p) : 0 < dos b r i := (by exact_mod_cast hd i : (0 : ℝ) < (dosBox b i).lo).trans_le
    (dos_enclosure b r h hw i).1
  unfold meshMetric
  apply div_pos _ (hwgt a.1)
  apply add_pos_of_pos_of_nonneg
  · unfold frequencyIndex
    push_cast
    positivity
  · apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (hwgt d.1).le (sub_nonneg.mpr (phonon_decreases _ _
      (sq_nonneg _) (realTransferSq_le t a.2 d.2) (h.2.1 _ _)))

theorem mesh_kernel_symm (r : Realization p) (cutoff : ℕ) (t : ℝ)
    (hm : ∀ i j, r.modes i j = r.modes j i) (hc : ∀ i j, r.coulomb i j = r.coulomb j i)
    (a d : p × Fin N) : meshKernel r cutoff t a d = meshKernel r cutoff t d a := by
  have he : realTransferSq t a.2 d.2 = realTransferSq t d.2 a.2 := by
    unfold realTransferSq
    congr 1 <;> ring
  dsimp only [meshKernel]
  rw [he, hm a.1 d.1, hc a.1 d.1]
  by_cases ha : a.2.val < cutoff ∧ d.2.val < cutoff
  · have hb : d.2.val < cutoff ∧ a.2.val < cutoff := ⟨ha.2, ha.1⟩
    simp only [ite_eq_left ha, ite_eq_left hb]
  · simp [ha, show ¬(d.2.val < cutoff ∧ a.2.val < cutoff) from fun h => ha ⟨h.2, h.1⟩]

theorem mesh_spectrum_continuous {p : Type} [Fintype p] (b : Mesh p) (r : Realization p)
    (h : b.matches r) (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (cutoff : ℕ) :
    Continuous fun t => spectrumTop (meshKernel r cutoff t) (meshMetric b r t : p × Fin N → ℝ) := by
  have hph (a d : p × Fin N) :
      (Continuous fun t => phononResponse (r.modes a.1 d.1) (realTransferSq t a.2 d.2).1) ∧
      (Continuous fun t => phononResponse (r.modes a.1 d.1) (realTransferSq t a.2 d.2).2) := by
    have hv := continuous_transfers a.2 d.2
    exact ⟨continuous_phonon _ _ (h.2.1 _ _) _ hv.1 (fun _ => sq_nonneg _),
      continuous_phonon _ _ (h.2.1 _ _) _ hv.2 (fun _ => sq_nonneg _)⟩
  apply spectrum_continuous
  · intro a d
    unfold meshKernel
    simp only
    split
    · exact ((hph a d).1.add (hph a d).2).sub continuous_const
    · exact (hph a d).1.add (hph a d).2
  · intro a
    unfold meshMetric
    apply Continuous.div_const
    exact continuous_const.add (continuous_finsetSum _ fun d _ =>
      continuous_const.mul ((hph a d).1.sub (hph a d).2))
  · exact mesh_metric_pos b r h hw hd

theorem mesh_crossing {p : Type} [Fintype p] (b : Mesh p) (r : Realization p)
    (h : b.matches r) (hw : 0 < b.halfWidth) (hd : ∀ i, 0 < (dosBox b i).lo)
    (cutoff : ℕ) {cold hot : ℝ} (hord : cold ≤ hot)
    (hlo : 1 ≤ spectrumTop (meshKernel r cutoff cold) (meshMetric b r cold : p × Fin N → ℝ))
    (hhi : spectrumTop (meshKernel r cutoff hot) (meshMetric b r hot : p × Fin N → ℝ) ≤ 1) :
    ∃ t ∈ Icc cold hot,
      spectrumTop (meshKernel r cutoff t) (meshMetric b r t : p × Fin N → ℝ) = 1 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hord
    (mesh_spectrum_continuous b r h hw hd cutoff (N := N)).continuousOn ⟨hhi, hlo⟩
  exact ⟨t, ht, he⟩

end Grain.Pairing.Material
