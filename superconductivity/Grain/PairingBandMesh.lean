import Grain.PairingMaterial
import Mathlib.MeasureTheory.Measure.Real

/-! A hard Fermi window admits a cellwise quadrature certificate even
at a window edge. The mass of edge cells is the uncertainty budget. -/

namespace Grain.Pairing.Material

open MeasureTheory Set

variable {α : Type} [MeasurableSpace α]

noncomputable def cellWindowWeight (μ : Measure α) (ξ : α → ℝ) (h : ℚ) (cell : Set α) : ℝ :=
  μ.real (cell ∩ {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h})

theorem cell_window_enclosure (μ : Measure α) [IsFiniteMeasure μ] (ξ : α → ℝ)
    (h : ℚ) (s : Sample) (cell : Set α) (hw : μ.real cell = s.weight)
    (he : ∀ x ∈ cell, s.energy.contains (ξ x)) :
    (windowSample h s).contains (cellWindowWeight μ ξ h cell) := by
  unfold windowSample cellWindowWeight
  split
  · rename_i hi
    have hlo : -(h : ℝ) ≤ s.energy.lo := by exact_mod_cast hi.1
    have hhi : (s.energy.hi : ℝ) ≤ h := by exact_mod_cast hi.2
    have hs : cell ∩ {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h} = cell :=
      inter_eq_left.mpr fun x hx => ⟨hlo.trans (he x hx).1, (he x hx).2.trans hhi⟩
    rw [hs, hw]
    exact Interval.point_contains _
  · split
    · rename_i ho
      have hs : cell ∩ {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx, hl, hu⟩
        rcases ho with h' | h'
        · have hlt : (s.energy.hi : ℝ) < -(h : ℝ) := by exact_mod_cast h'
          exact (not_lt_of_ge (hl.trans (he x hx).2)) hlt
        · have hlt : (h : ℝ) < s.energy.lo := by exact_mod_cast h'
          exact (not_lt_of_ge ((he x hx).1.trans hu)) hlt
      simp [hs, Interval.point, Interval.contains]
    · constructor
      · simp only [Rat.cast_zero]
        exact (measureReal_nonneg (μ := μ) (s := cell ∩ {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h}))
      · change _ ≤ (s.weight : ℝ)
        rw [← hw]
        exact measureReal_mono inter_subset_left

/-- The bound applies to the sum of true window masses on a patch's
cells. The caller supplies a measurable partition of the patch when
interpreting this sum as a Brillouin-zone integral. -/
theorem band_mesh_enclosure (μ : Measure α) [IsFiniteMeasure μ] (ξ : α → ℝ)
    (h : ℚ) (hh : 0 < h) (samples : List Sample) (cells : List (Set α))
    (hcell : List.Forall₂ (fun s cell => μ.real cell = (s.weight : ℝ) ∧
      ∀ x ∈ cell, s.energy.contains (ξ x)) samples cells) :
    (weightBox h samples).contains
      ((cells.map (cellWindowWeight μ ξ h)).sum / (2 * (h : ℝ))) := by
  have hc : List.Forall₂ Interval.contains (samples.map (windowSample h))
      (cells.map (cellWindowWeight μ ξ h)) := by
    induction hcell with
    | nil => exact .nil
    | cons hb _ ih => exact .cons (cell_window_enclosure μ ξ h _ _ hb.1 hb.2) ih
  have hlo : 0 ≤ (Interval.sumList (samples.map (windowSample h))).lo := by
    clear hc
    induction hcell with
    | nil => exact le_rfl
    | @cons s cell _ _ hs _ ih =>
      refine add_nonneg ?_ ih
      have hw : (0 : ℝ) ≤ s.weight := hs.1 ▸ measureReal_nonneg
      unfold windowSample
      split
      · exact_mod_cast hw
      · split <;> exact le_rfl
  simpa [weightBox] using Interval.div_contains hlo (by change 0 < 2 * h; positivity)
    (Interval.sumList_contains hc) (Interval.point_contains (2 * h))

/-- For a measurable partition the sum of cell window masses equals the
actual patch window mass. -/
theorem band_mesh_partition (μ : Measure α) [IsFiniteMeasure μ] (ξ : α → ℝ)
    (h : ℚ) (cells : List (Set α)) (patch : Set α)
    (hpatch : (⋃ i : Fin cells.length, cells.get i) = patch)
    (hdisj : Pairwise (fun i j : Fin cells.length => Disjoint (cells.get i) (cells.get j)))
    (hcell : ∀ i : Fin cells.length, MeasurableSet (cells.get i))
    (hwin : MeasurableSet {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h}) :
    (cells.map (cellWindowWeight μ ξ h)).sum = cellWindowWeight μ ξ h patch := by
  let window : Set α := {x | -(h : ℝ) ≤ ξ x ∧ ξ x ≤ h}
  have hg : (⋃ i : Fin cells.length, cells.get i ∩ window) = patch ∩ window := by
    rw [← hpatch]
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    aesop
  have hs : (cells.map (cellWindowWeight μ ξ h)).sum =
      ∑ i : Fin cells.length, μ.real (cells.get i ∩ window) := by
    calc
      _ = ((List.ofFn cells.get).map (cellWindowWeight μ ξ h)).sum := by rw [List.ofFn_get]
      _ = _ := by rw [List.map_ofFn, List.sum_ofFn]; rfl
  rw [hs, cellWindowWeight, ← hg]
  exact (measureReal_iUnion_fintype
    (fun _ _ hij => (hdisj hij).mono inter_subset_left inter_subset_left)
    (fun i => (hcell i).inter hwin) (fun _ => measure_ne_top _ _)).symm

/-- Feed certified cell-integrated DOS values into the same kernel and
metric enclosures as point samples. -/
theorem band_mesh_realization {p : Type} (b : Mesh p) (r : Realization p)
    (hr : b.matches r) (hw : 0 < b.halfWidth) (μ : Measure α) [IsFiniteMeasure μ]
    (ξ : α → ℝ) (cells : p → List (Set α))
    (hcell : ∀ i, List.Forall₂ (fun s cell => μ.real cell = (s.weight : ℝ) ∧
      ∀ x ∈ cell, s.energy.contains (ξ x)) (b.bands i) (cells i)) :
    b.matches { r with integratedDOS := some (fun i =>
      ((cells i).map (cellWindowWeight μ ξ b.halfWidth)).sum / (2 * (b.halfWidth : ℝ))) } := by
  exact ⟨fun i => band_mesh_enclosure μ ξ _ hw _ _ (hcell i), hr.2⟩

end Grain.Pairing.Material
