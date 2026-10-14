import VerifiedPhysics.Certificates.MaxwellBounds
import VerifiedPhysics.CrossScale.MaxwellElimination
import VerifiedPhysics.Atomistic.BiasedHessian

namespace VerifiedPhysics.MaxwellSlab

/-- At least 3/5 of the magnetic-field energy is within distance one of
the interface, in a box extending to distance two on either side. The
common volume and permeability factors cancel. -/
def MagneticEnergyLocalized (f : Fields) : Prop :=
  (∑ j ∈ Finset.range 8, (f.vacuumH j ^ 2 + f.materialH j ^ 2)) ≤
    (2 / 5 : ℝ) * ∑ j ∈ Finset.range 16, (f.vacuumH j ^ 2 + f.materialH j ^ 2)

theorem scaled_profile_tail (q a : ℝ) (hq : 2 ≤ q)
    (ht : 8 * profile q 7 ^ 2 ≤ (2/5 : ℝ) * profile q 15 ^ 2) :
    (∑ j ∈ Finset.range 8, (a * profile q j) ^ 2) ≤
      (2/5 : ℝ) * (a * profile q 15) ^ 2 := by
  have hm : Monotone (profile q) := monotone_nat_of_le_succ (fun j => (profile_positive_mono q hq j).2)
  calc
    _ ≤ ∑ j ∈ Finset.range 8, a ^ 2 * profile q 7 ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hj' : j ≤ 7 := by have := Finset.mem_range.mp hj; omega
      exact pow_le_pow_left₀ (by linarith [(profile_positive_mono q hq j).1]) (hm hj') 2
    _ = a ^ 2 * (8 * profile q 7 ^ 2) := by simp; ring
    _ ≤ a ^ 2 * ((2/5 : ℝ) * profile q 15 ^ 2) := mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = _ := by ring

theorem certified_localization (b s : ℝ)
    (hb : b ∈ Set.Icc (1999999/1000000 : ℝ) (2000001/1000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    MagneticEnergyLocalized (reconstruct b s (vacuumWitness b s) (materialWitness b s)) := by
  obtain ⟨_, _, _, hv, hm⟩ := domain_bounds b s hb hs
  obtain ⟨htv, htm⟩ := profile_localization_bounds b s hb hs
  have tv := scaled_profile_tail (qVac s)
    (interfaceCoupling b s * profile (qMat b s) 15) (by linarith [hv.1]) htv
  have tm := scaled_profile_tail (qMat b s) (leftResidual b s) (by linarith [hm.1]) htm
  change (∑ j ∈ Finset.range 8, (vacuumWitness b s j)^2) ≤ _ at tv
  change (∑ j ∈ Finset.range 8, (materialWitness b s j)^2) ≤ _ at tm
  have hsum : vacuumWitness b s 15 ^ 2 + materialWitness b s 15 ^ 2 ≤
      ∑ j ∈ Finset.range 16, (vacuumWitness b s j ^ 2 + materialWitness b s j ^ 2) := by
    apply Finset.single_le_sum (f := fun j : ℕ => vacuumWitness b s j ^ 2 + materialWitness b s j ^ 2)
    · intro j _; positivity
    · simp
  unfold MagneticEnergyLocalized
  dsimp [reconstruct]
  rw [Finset.sum_add_distrib]
  dsimp [vacuumWitness, materialWitness] at tv tm hsum ⊢
  nlinarith

/-- The certified field mode also moves the material ions; it is not a
vacuum cavity mode with a vanishing material displacement. -/
theorem certified_material_motion (b s : ℝ)
    (hb : b ∈ Set.Icc (1999999/1000000 : ℝ) (2000001/1000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    (reconstruct b s (vacuumWitness b s) (materialWitness b s)).normalIon 15 ≠ 0 := by
  obtain ⟨hd, he, hi, hv, hm⟩ := domain_bounds b s hb hs
  have hqi : -0.5 < epsInterface b s := by
    have h := (dielectric_intervals b s 3.01 3.012 hb hs (by norm_num)).2.1
    linarith
  have hc : interfaceCoupling b s < -128 := by
    unfold interfaceCoupling
    apply (div_lt_iff_of_neg hi).2
    linarith
  have hpv : 0 < profile (qVac s) 15 := by
    linarith [(profile_positive_mono (qVac s) (by linarith [hv.1]) 15).1]
  have hpv14 : 0 < profile (qVac s) 14 := by
    linarith [(profile_positive_mono (qVac s) (by linarith [hv.1]) 14).1]
  have hpm : 0 < profile (qMat b s) 15 := by
    linarith [(profile_positive_mono (qMat b s) (by linarith [hm.1]) 15).1]
  have hleft : leftResidual b s < 0 := by
    unfold leftResidual
    have hn : 64+6-s+interfaceCoupling b s < 0 := by linarith [hs.1]
    have := mul_neg_of_neg_of_pos hn hpv
    nlinarith
  have hmat : materialWitness b s 15 ≠ 0 :=
    mul_ne_zero (ne_of_lt hleft) (ne_of_gt hpm)
  exact div_ne_zero (div_ne_zero hmat (ne_of_lt he)) hd

/-- A finite Maxwell-ion surface mode, with a checked frequency enclosure
uniform over a nonzero interval of microscopic Hessians. -/
theorem certified_maxwell_ionic_surface (b : ℝ)
    (hb : b ∈ Set.Icc (1999999/1000000 : ℝ) (2000001/1000000 : ℝ)) :
    ∃ s : ℝ, ∃ f : Fields,
      s ∈ Set.Icc (3.01 : ℝ) 3.012 ∧ MaxwellIonMode b s f ∧
      MagneticEnergyLocalized f ∧ f.normalIon 15 ≠ 0 := by
  obtain ⟨s, hs, hroot⟩ := certified_root b hb
  obtain ⟨hd, he, hi, hv, hm⟩ := domain_bounds b s hb hs
  refine ⟨s, reconstruct b s (vacuumWitness b s) (materialWitness b s), hs, ?_,
    certified_localization b s hb hs, certified_material_motion b s hb hs⟩
  apply reconstruct_ionic_mode b s _ _ hd (ne_of_lt he) (ne_of_lt hi)
  exact root_magnetic_mode b s (ne_of_lt he) (ne_of_lt hi)
    (by linarith [hv.1]) (by linarith [hm.1]) hroot

theorem frequency_error (s : ℝ) (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    0 < Real.sqrt s - Real.sqrt 3 ∧
    |Real.sqrt s - Real.sqrt 3| ≤ (1/250 : ℝ) := by
  have hs0 : 0 ≤ s := by linarith [hs.1]
  have hsq := Real.sq_sqrt hs0
  have hthree := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg s
  have hn3 := Real.sqrt_nonneg (3 : ℝ)
  have hlo : (3/2 : ℝ) < Real.sqrt 3 := by nlinarith
  have hpos : 0 < Real.sqrt s - Real.sqrt 3 := by nlinarith [hs.1]
  refine ⟨hpos, ?_⟩
  rw [abs_of_pos hpos]
  nlinarith [hs.2]

end VerifiedPhysics.MaxwellSlab
