import Grain.Pairing

/-! Static phonon attraction and channel removal in a two-band pairing model. -/

namespace Grain.Pairing.Attribution

/-- Each summand is the zero-transfer phonon exchange. With a mass-weighted
  derivative A and g = A / √(2Ω), its weight is |A|² / Ω². -/
theorem phonon_zero (data : Input p) (i j : p)
    (h : ∀ mode ∈ data.modes i j, 0 < mode.energy) :
    phonon data i j 0 = ((data.modes i j).map fun mode => 2 * mode.vertexSq / mode.energy).sum := by
  unfold phonon
  congr 1
  apply List.map_congr_left
  intro mode hm
  have hn := (h mode hm).ne'
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero]
  field_simp

theorem static_mode_from_derivative (energy derivativeSq : ℚ) (h : 0 < energy) :
    2 * (derivativeSq / (2 * energy)) / energy = derivativeSq / energy^2 := by
  field_simp

/-- The block-average pairing interaction is weighted on both Fermi sheets.
  The row is divided by its total density of states, so the column density
  of states is already included in the resulting gap-equation coefficient. -/
def bandCoupling (dos : i → ℚ) (interaction : i → i → ℚ)
    (row col : Finset i) : ℚ :=
  (∑ a ∈ row, ∑ b ∈ col, dos a * interaction a b * dos b) / (∑ a ∈ row, dos a)

/-- Symmetric form of the static sheet kernel with diagonal metric `dos`.
  Restricting the trial gap to be constant on each group gives the block
  averages used in `bandCoupling`. -/
def sheetKernel (dos : i → ℚ) (interaction : i → i → ℚ) (a b : i) : ℚ :=
  dos a * interaction a b * dos b

structure Coupling where
  aa : ℚ
  ab : ℚ
  ba : ℚ
  bb : ℚ

namespace Coupling

def block (dos : i → ℚ) (interaction : i → i → ℚ) (a b : Finset i) : Coupling :=
  ⟨bandCoupling dos interaction a a, bandCoupling dos interaction a b,
    bandCoupling dos interaction b a, bandCoupling dos interaction b b⟩

def withoutFirst (k : Coupling) : Coupling := ⟨0, k.ab, k.ba, k.bb⟩
def withoutSecond (k : Coupling) : Coupling := ⟨k.aa, k.ab, k.ba, 0⟩
def withoutInterband (k : Coupling) : Coupling := ⟨k.aa, 0, 0, k.bb⟩

def EntrywiseLE (x y : Coupling) : Prop :=
  x.aa ≤ y.aa ∧ x.ab ≤ y.ab ∧ x.ba ≤ y.ba ∧ x.bb ≤ y.bb

/-- The larger root of the characteristic polynomial. For nonnegative
  entries it is the spectral radius of the two-band attraction matrix. -/
noncomputable def leading (k : Coupling) : ℝ :=
  ((k.aa : ℝ) + k.bb + √(((k.aa : ℝ) - k.bb)^2 + 4 * k.ab * k.ba)) / 2

theorem leading_spec (k : Coupling) (hb : 0 ≤ k.ab) (hc : 0 ≤ k.ba) :
    (k.aa : ℝ) ≤ k.leading ∧ (k.bb : ℝ) ≤ k.leading ∧
    (k.leading - k.aa) * (k.leading - k.bb) = (k.ab : ℝ) * k.ba := by
  have hbc : 0 ≤ (k.ab : ℝ) * k.ba := mul_nonneg (by exact_mod_cast hb) (by exact_mod_cast hc)
  let t : ℝ := (k.aa : ℝ) - k.bb
  let r : ℝ := √(t^2 + 4 * ((k.ab : ℝ) * k.ba))
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = t^2 + 4 * ((k.ab : ℝ) * k.ba) :=
    Real.sq_sqrt (by positivity)
  have hr : |t| ≤ r := by
    apply nonneg_le_nonneg_of_sq_le_sq hr0
    rw [← sq, ← sq, sq_abs, hr2]
    linarith
  have ht := (abs_le.mp hr)
  have eq : k.leading = ((k.aa : ℝ) + k.bb + r) / 2 := by
    unfold leading r t
    congr 3
    ring
  rw [eq]
  dsimp [t] at ht hr2
  refine ⟨by linarith [ht.2], by linarith [ht.1], ?_⟩
  nlinarith [hr2]

private theorem leading_le (k : Coupling) (hb : 0 ≤ k.ab) (hc : 0 ≤ k.ba) {t : ℝ}
    (ha : (k.aa : ℝ) ≤ t) (hd : (k.bb : ℝ) ≤ t)
    (h : (k.ab : ℝ) * k.ba ≤ (t - k.aa) * (t - k.bb)) : k.leading ≤ t := by
  obtain ⟨hka, hkd, he⟩ := leading_spec k hb hc
  by_contra! ht
  have hpos := mul_pos (sub_pos.mpr ht) (sub_pos.mpr ht)
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.le) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg (sub_nonneg.mpr ht.le) (sub_nonneg.mpr hd)
  nlinarith only [h, he, hpos, h₁, h₂]

theorem leading_mono {x y : Coupling} (hb : 0 ≤ x.ab) (hc : 0 ≤ x.ba)
    (h : EntrywiseLE x y) : x.leading ≤ y.leading := by
  obtain ⟨ha, hab, hba, hd⟩ := h
  obtain ⟨hya, hyd, he⟩ := leading_spec y (hb.trans hab) (hc.trans hba)
  have hax : (x.aa : ℝ) ≤ y.aa := by exact_mod_cast ha
  have hdx : (x.bb : ℝ) ≤ y.bb := by exact_mod_cast hd
  apply leading_le x hb hc (hax.trans hya) (hdx.trans hyd)
  calc
    (x.ab : ℝ) * x.ba ≤ (y.ab : ℝ) * y.ba := by
      exact_mod_cast mul_le_mul hab hba hc (hb.trans hab)
    _ = (y.leading - y.aa) * (y.leading - y.bb) := he.symm
    _ ≤ (y.leading - x.aa) * (y.leading - x.bb) :=
      mul_le_mul (sub_le_sub_left hax _) (sub_le_sub_left hdx _) (sub_nonneg.mpr hyd)
        (sub_nonneg.mpr (hax.trans hya))

/-- A rational bracket can be checked without evaluating a square root. -/
theorem leading_bounds (k : Coupling) (l u : ℚ)
    (hb : 0 ≤ k.ab) (hc : 0 ≤ k.ba)
    (hl : l ≤ k.aa ∨ l ≤ k.bb ∨ (l - k.aa) * (l - k.bb) ≤ k.ab * k.ba)
    (hu : k.aa ≤ u ∧ k.bb ≤ u ∧ k.ab * k.ba ≤ (u - k.aa) * (u - k.bb)) :
    (l : ℝ) ≤ k.leading ∧ k.leading ≤ (u : ℝ) := by
  obtain ⟨ha, hd, he⟩ := leading_spec k hb hc
  refine ⟨?_, leading_le k hb hc (by exact_mod_cast hu.1) (by exact_mod_cast hu.2.1) ?_⟩
  · rcases hl with hl | hl | hl
    · exact (by exact_mod_cast hl : (l : ℝ) ≤ k.aa).trans ha
    · exact (by exact_mod_cast hl : (l : ℝ) ≤ k.bb).trans hd
    · have hl' : ((l : ℝ) - k.aa) * ((l : ℝ) - k.bb) ≤ (k.ab : ℝ) * k.ba := by
        exact_mod_cast hl
      by_contra! ht
      have hpos := mul_pos (sub_pos.mpr ht) (sub_pos.mpr ht)
      have h₁ := mul_nonneg (sub_nonneg.mpr ht.le) (sub_nonneg.mpr ha)
      have h₂ := mul_nonneg (sub_nonneg.mpr ht.le) (sub_nonneg.mpr hd)
      nlinarith only [hl', he, hpos, h₁, h₂]
  · exact_mod_cast hu.2.2

theorem withoutFirst_mono {x y : Coupling} (hb : 0 ≤ x.ab) (hc : 0 ≤ x.ba)
    (h : EntrywiseLE x y) : x.withoutFirst.leading ≤ y.withoutFirst.leading :=
  leading_mono hb hc ⟨le_rfl, h.2.1, h.2.2.1, h.2.2.2⟩

/-- If removing the first intraband channel takes the leading coupling
  below that channel's diagonal, its removal has the largest effect. -/
theorem first_dominates (k : Coupling) (hb : 0 ≤ k.ab) (hc : 0 ≤ k.ba)
    (h : k.withoutFirst.leading < (k.aa : ℝ)) :
    k.withoutFirst.leading < k.withoutSecond.leading ∧
    k.withoutFirst.leading < k.withoutInterband.leading :=
  ⟨h.trans_le (leading_spec k.withoutSecond hb hc).1,
    h.trans_le (leading_spec k.withoutInterband (by simp [withoutInterband])
      (by simp [withoutInterband])).1⟩

end Coupling
end Grain.Pairing.Attribution
