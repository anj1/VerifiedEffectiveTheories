import GrandCanonicalPRG

/-!
The final finite-volume, two-scale statement.  Its endpoint Binder signs and
structure-factor enclosures are explicit *premises*, supplied by statistical
certificates conditional on iid perfect-sampling streams.  This file proves
only their deterministic physical consequences; no random-source property,
concentration inequality, infinite-volume critical point, or exponent is
silently assumed.
-/
namespace GrandCanonical

open LatticeGas

/-- A positive spin contributes +1 to the axial Fourier amplitude. -/
noncomputable def axialCoordinate {L : ℕ} (x : Site L) (axis : Fin 3) : ℝ :=
  if axis = 0 then x.1.val else if axis = 1 then x.2.1.val else x.2.2.val

/-- Spin Fourier amplitude at the first nonzero axial mode, `2π/L`. -/
noncomputable def axialAmplitude (L : ℕ) (axis : Fin 3) (s : Spin L) : ℂ :=
  ∑ x : Site L, (if s x then (1 : ℂ) else -1) *
    Complex.exp (((2 * Real.pi * axialCoordinate x axis / (L : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The three-axis average of the first spin-mode powers, normalized by volume. -/
noncomputable def axialPower (L : ℕ) (s : Spin L) : ℝ :=
  (∑ axis : Fin 3, ‖axialAmplitude L axis s‖ ^ 2) / (3 * (L : ℝ) ^ 3)

/-- Population spin structure factor at each box's own lowest axial wavevector. -/
noncomputable def populationAxialS (L : ℕ) (r : ℝ) : ℝ :=
  realExpectation (axialPower L) r

/-- The exact finite-volume population Binder curve. Raw magnetization moments
give the same cumulant as magnetization divided by `L³`. -/
noncomputable def populationBinder (L : ℕ) (r : ℝ) : ℝ :=
  realBinder (L := L) magnetizationSq magnetizationFourth r

/-- Two certified endpoint sign changes yield nested finite-volume crossings.
The eight decimal S endpoints are outward enclosures of the existing rational
statistical certificates, not measured values asserted by the Lean kernel.
The parameters `16/25` and `34/53` are frozen near-crossing *sampling*
parameters, not asserted to equal either exact Binder crossing. -/
theorem two_scale_pseudocriticality_and_amplification
    (h46low : populationBinder 4 (12 / 19) < populationBinder 6 (12 / 19))
    (h46high : populationBinder 6 (11 / 17) < populationBinder 4 (11 / 17))
    (h812low : populationBinder 8 (7 / 11) < populationBinder 12 (7 / 11))
    (h812high : populationBinder 12 (20 / 31) < populationBinder 8 (20 / 31))
    (hS4lo : (1.460341 : ℝ) < populationAxialS 4 (16 / 25))
    (hS4hi : populationAxialS 4 (16 / 25) < (1.565010 : ℝ))
    (hS6lo : (2.930119 : ℝ) < populationAxialS 6 (16 / 25))
    (hS6hi : populationAxialS 6 (16 / 25) < (3.218483 : ℝ))
    (hS8lo : (4.637165 : ℝ) < populationAxialS 8 (34 / 53))
    (hS8hi : populationAxialS 8 (34 / 53) < (6.060436 : ℝ))
    (hS12lo : (9.449947 : ℝ) < populationAxialS 12 (34 / 53))
    (hS12hi : populationAxialS 12 (34 / 53) < (13.977288 : ℝ)) :
    (∃ r46 r812 : ℝ,
      12 / 19 < r46 ∧ r46 < 11 / 17 ∧
      populationBinder 4 r46 = populationBinder 6 r46 ∧
      7 / 11 < r812 ∧ r812 < 20 / 31 ∧
      populationBinder 8 r812 = populationBinder 12 r812 ∧
      |r46 - r812| < 8 / 589) ∧
    (7 / 11 : ℝ) > 12 / 19 ∧ (20 / 31 : ℝ) < 11 / 17 ∧
    Set.Ioo (7 / 11 : ℝ) (20 / 31 : ℝ) ⊆
      Set.Ioo (12 / 19 : ℝ) (11 / 17 : ℝ) ∧
    (1.872 : ℝ) < populationAxialS 6 (16 / 25) / populationAxialS 4 (16 / 25) ∧
      populationAxialS 6 (16 / 25) / populationAxialS 4 (16 / 25) < (2.204 : ℝ) ∧
    (1.559 : ℝ) < populationAxialS 12 (34 / 53) / populationAxialS 8 (34 / 53) ∧
      populationAxialS 12 (34 / 53) / populationAxialS 8 (34 / 53) < (3.015 : ℝ) := by
  have hcross46 : ∃ r ∈ Set.Ioo (12 / 19 : ℝ) (11 / 17 : ℝ),
      populationBinder 4 r = populationBinder 6 r := by
    simpa [populationBinder, sub_neg, sub_pos] using
      (isingBinder_crossing (L₁ := 4) (L₂ := 6)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (sub_neg.mpr h46low) (sub_pos.mpr h46high))
  have hcross812 : ∃ r ∈ Set.Ioo (7 / 11 : ℝ) (20 / 31 : ℝ),
      populationBinder 8 r = populationBinder 12 r := by
    simpa [populationBinder] using
      (isingBinder_crossing (L₁ := 8) (L₂ := 12)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (sub_neg.mpr h812low) (sub_pos.mpr h812high))
  rcases hcross46 with ⟨r46, ⟨h46a, h46b⟩, heq46⟩
  rcases hcross812 with ⟨r812, ⟨h812a, h812b⟩, heq812⟩
  have hsep : |r46 - r812| < (8 / 589 : ℝ) := by
    rw [abs_lt]
    constructor <;> norm_num at * <;> linarith
  have hS4pos : (0 : ℝ) < populationAxialS 4 (16 / 25) := by linarith
  have hS8pos : (0 : ℝ) < populationAxialS 8 (34 / 53) := by linarith
  refine ⟨⟨r46, r812, h46a, h46b, heq46, h812a, h812b, heq812, hsep⟩,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor <;> norm_num at * <;> linarith
  · apply (lt_div_iff₀ hS4pos).2
    nlinarith [hS4hi, hS6lo]
  · apply (div_lt_iff₀ hS4pos).2
    nlinarith [hS4lo, hS6hi]
  · apply (lt_div_iff₀ hS8pos).2
    nlinarith [hS8hi, hS12lo]
  · apply (div_lt_iff₀ hS8pos).2
    nlinarith [hS8lo, hS12hi]

/-- The union-bound bookkeeping for the three *separate* 95%-coverage
families: the 4→6 endpoint signs, the 8→12 endpoint signs, and the four
scattering means.  The individual 95% premises rely on an external
concentration theorem and ideal iid equilibrium sampling; this theorem does
not manufacture those premises from a deterministic PRNG. -/
theorem three_familywise_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (A B C : Set Ω) (hBmeas : MeasurableSet B) (hCmeas : MeasurableSet C)
    (hA : (0.95 : ℝ) ≤ μ.real A)
    (hB : (0.95 : ℝ) ≤ μ.real B)
    (hC : (0.95 : ℝ) ≤ μ.real C) :
    (0.85 : ℝ) ≤ μ.real ((A ∩ B) ∩ C) := by
  have pair_bound (X Y : Set Ω) (hYmeas : MeasurableSet Y)
      {α β : ℝ} (hX : 1 - α ≤ μ.real X)
      (hY : 1 - β ≤ μ.real Y) :
      1 - (α + β) ≤ μ.real (X ∩ Y) := by
    have hU : μ.real (X ∪ Y) ≤ 1 := by
      calc
        μ.real (X ∪ Y) ≤ μ.real Set.univ :=
          MeasureTheory.measureReal_mono (Set.subset_univ _)
        _ = 1 := MeasureTheory.probReal_univ
    have hsum := MeasureTheory.measureReal_union_add_inter₀
      hYmeas.nullMeasurableSet (s := X) (t := Y)
      (MeasureTheory.measure_ne_top μ X) (MeasureTheory.measure_ne_top μ Y)
    linarith
  have hAB : (0.90 : ℝ) ≤ μ.real (A ∩ B) := by
    have h := pair_bound A B hBmeas (α := (0.05 : ℝ))
      (β := (0.05 : ℝ)) (by linarith) (by linarith)
    norm_num at h ⊢
    exact h
  have h := pair_bound (A ∩ B) C hCmeas (α := (0.10 : ℝ))
    (β := (0.05 : ℝ)) (by linarith) (by linarith)
  norm_num at h ⊢
  exact h

end GrandCanonical
