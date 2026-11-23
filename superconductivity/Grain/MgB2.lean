import Grain.MgB2Data

/-! Channel attribution from independently calculated electronic-structure
  inputs for MgB₂. The eigenvalues concern the static phonon-only models. -/

namespace Grain.Pairing.Attribution.MgB2

theorem sensitivity_box (k source : Coupling) (hsource : source = liu ∨ source = brinkman)
    (ha : |k.aa - source.aa| ≤ sensitivity) (hb : |k.ab - source.ab| ≤ sensitivity)
    (hc : |k.ba - source.ba| ≤ sensitivity) (hd : |k.bb - source.bb| ≤ sensitivity) :
    minSigma ≤ k.aa ∧ k.EntrywiseLE upper := by
  have hbox : minSigma ≤ source.aa - sensitivity ∧ source.aa + sensitivity ≤ upper.aa ∧
      source.ab + sensitivity ≤ upper.ab ∧ source.ba + sensitivity ≤ upper.ba ∧
      source.bb + sensitivity ≤ upper.bb := by
    rcases hsource with rfl | rfl <;> decide +kernel
  obtain ⟨hmin, hmax, hab, hba, hbb⟩ := hbox
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linarith [(abs_le.mp ha).1]
  · linarith [(abs_le.mp ha).2]
  · linarith [(abs_le.mp hb).2]
  · linarith [(abs_le.mp hc).2]
  · linarith [(abs_le.mp hd).2]

/-- The two-band conclusion holds for independent variation of the entries
  under the stated bounds, which include both published calculations. -/
theorem sigma_dominates_two_band (k source : Coupling) (hsource : source = liu ∨ source = brinkman)
    (ha : |k.aa - source.aa| ≤ sensitivity) (hb : |k.ab - source.ab| ≤ sensitivity)
    (hc : |k.ba - source.ba| ≤ sensitivity) (hd : |k.bb - source.bb| ≤ sensitivity)
    (hb0 : 0 ≤ k.ab) (hc0 : 0 ≤ k.ba) :
    k.withoutFirst.leading < k.withoutSecond.leading ∧
    k.withoutFirst.leading < k.withoutInterband.leading ∧
    (9/50 : ℝ) < k.leading - k.withoutFirst.leading := by
  obtain ⟨hσ, h⟩ := sensitivity_box k source hsource ha hb hc hd
  have hlo : (minSigma : ℝ) ≤ k.aa := by exact_mod_cast hσ
  have hhi := (Coupling.withoutFirst_mono hb0 hc0 h).trans upper_withoutSigma
  have hcoup := (Coupling.leading_spec k hb0 hc0).1
  norm_num [minSigma] at hlo hhi
  obtain ⟨h₁, h₂⟩ := Coupling.first_dominates k hb0 hc0 (by linarith)
  exact ⟨h₁, h₂, by linarith⟩

theorem sigma_dominates_four_sheet :
    Pairing.leading sheet_withoutSigma dos < Pairing.leading sheet_withoutPi dos ∧
    Pairing.leading sheet_withoutSigma dos < Pairing.leading sheet_withoutInterband dos := by
  have hσ := sheet_withoutSigma_bounds.2
  have hπ := sheet_withoutPi_bounds.1
  have hinter := sheet_withoutInterband_bounds.1
  norm_num at hσ hπ hinter
  constructor <;> linarith

theorem grouping_full_error :
    0 < Pairing.leading sheet_full dos - liu.leading ∧
    Pairing.leading sheet_full dos - liu.leading < (3/1000 : ℝ) := by
  have ⟨hlo, hhi⟩ := sheet_full_bounds
  have ⟨h₂lo, h₂hi⟩ := liu_full
  norm_num at hlo hhi h₂lo h₂hi
  constructor <;> linarith

/-- The two degenerate branches are counted together. Each computed branch
  also lies in the reported X-ray interval for an individual component. -/
theorem a_point_e2g_dominates :
    (93/100 : ℚ) * (∑ i, aPointMode i) < ∑ i ∈ aPointE2g, aPointMode i := by
  decide +kernel

theorem a_point_xray_compatible :
    ∀ i ∈ aPointE2g, xrayCenter - xrayError ≤ aPointMode i ∧
      aPointMode i ≤ xrayCenter + xrayError := by
  decide +kernel

end Grain.Pairing.Attribution.MgB2
