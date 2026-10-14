import VerifiedPhysics.Certificates.MaxwellProfiles

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace VerifiedPhysics.MaxwellSlab

theorem inverse_negative_interval {x l u : ℝ} (h : x ∈ Set.Icc l u) (hu : u < 0) :
    x⁻¹ ∈ Set.Icc u⁻¹ l⁻¹ := by
  have hx : x < 0 := lt_of_le_of_lt h.2 hu
  have hl : l < 0 := lt_of_le_of_lt h.1 hx
  exact ⟨(inv_le_inv_of_neg hu hx).2 h.2, (inv_le_inv_of_neg hx hl).2 h.1⟩

theorem dielectric_intervals (b s sl su : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ))
    (hs : s ∈ Set.Icc sl su) (hsep : (2000001 / 1000000 : ℝ) - sl < 0) :
    eps b s ∈ Set.Icc (1 + 3 / ((2000001 / 1000000 : ℝ) - sl))
      (1 + 3 / ((1999999 / 1000000 : ℝ) - su)) ∧
    epsInterface b s ∈ Set.Icc (1 + (3 / 2 : ℝ) / ((2000001 / 1000000 : ℝ) - sl))
      (1 + (3 / 2 : ℝ) / ((1999999 / 1000000 : ℝ) - su)) := by
  have hd : b-s ∈ Set.Icc ((1999999 / 1000000 : ℝ)-su) ((2000001 / 1000000 : ℝ)-sl) :=
    ⟨by linarith [hb.1, hs.2], by linarith [hb.2, hs.1]⟩
  have hi := inverse_negative_interval hd hsep
  dsimp [eps, epsInterface]
  simp only [div_eq_mul_inv]
  constructor <;> constructor <;> nlinarith [hi.1, hi.2]

theorem lower_sign (b : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ)) :
    characteristic b 3.01 < 0 := by
  obtain ⟨her, hir⟩ := dielectric_intervals b 3.01 3.01 3.01
    hb ⟨le_rfl, le_rfl⟩ (by norm_num)
  have he : eps b 3.01 ∈ Set.Icc (-1.9703000) (-1.9702940) :=
    ⟨le_trans (by norm_num) her.1, le_trans her.2 (by norm_num)⟩
  have heir := inverse_negative_interval her (by norm_num)
  have hiir := inverse_negative_interval hir (by norm_num)
  have hei : (eps b 3.01)⁻¹ ∈ Set.Icc (-0.50753846) (-0.50753692) :=
    ⟨le_trans (by norm_num) heir.1, le_trans heir.2 (by norm_num)⟩
  have hii : (epsInterface b 3.01)⁻¹ ∈ Set.Icc (-2.06123075) (-2.06121823) :=
    ⟨le_trans (by norm_num) hiir.1, le_trans hiir.2 (by norm_num)⟩
  have hqv : qVac 3.01 = 2.04671875 := by norm_num [qVac]
  have hqm : qMat b 3.01 ∈ Set.Icc 2.18641538 2.18641568 := by
    unfold qMat
    rw [div_eq_mul_inv, show (64 : ℝ)⁻¹ = 0.015625 by norm_num]
    dyadic_interval [prec := 100]
  unfold characteristic leftResidual rightResidual
  simp only [profile14, profile15, hqv]
  unfold profilePolynomial14 profilePolynomial15 interfaceCoupling
  simp only [div_eq_mul_inv, pow_two]
  generalize (eps b 3.01)⁻¹ = e at hei ⊢
  generalize (epsInterface b 3.01)⁻¹ = i at hii ⊢
  generalize qMat b 3.01 = q at hqm ⊢
  dyadic_interval [prec := 100]

theorem upper_sign (b : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ)) :
    0 < characteristic b 3.012 := by
  obtain ⟨her, hir⟩ := dielectric_intervals b 3.012 3.012 3.012
    hb ⟨le_rfl, le_rfl⟩ (by norm_num)
  have he : eps b 3.012 ∈ Set.Icc (-1.96442981) (-1.96442394) :=
    ⟨le_trans (by norm_num) her.1, le_trans her.2 (by norm_num)⟩
  have heir := inverse_negative_interval her (by norm_num)
  have hiir := inverse_negative_interval hir (by norm_num)
  have hei : (eps b 3.012)⁻¹ ∈ Set.Icc (-0.50905510) (-0.50905355) :=
    ⟨le_trans (by norm_num) heir.1, le_trans heir.2 (by norm_num)⟩
  have hii : (epsInterface b 3.012)⁻¹ ∈ Set.Icc (-2.07377681) (-2.07376418) :=
    ⟨le_trans (by norm_num) hiir.1, le_trans hiir.2 (by norm_num)⟩
  have hqv : qVac 3.012 = 2.0466875 := by norm_num [qVac]
  have hqm : qMat b 3.012 ∈ Set.Icc 2.18620069 2.18620099 := by
    unfold qMat
    rw [div_eq_mul_inv, show (64 : ℝ)⁻¹ = 0.015625 by norm_num]
    dyadic_interval [prec := 100]
  unfold characteristic leftResidual rightResidual
  simp only [profile14, profile15, hqv]
  unfold profilePolynomial14 profilePolynomial15 interfaceCoupling
  simp only [div_eq_mul_inv, pow_two]
  generalize (eps b 3.012)⁻¹ = e at hei ⊢
  generalize (epsInterface b 3.012)⁻¹ = i at hii ⊢
  generalize qMat b 3.012 = q at hqm ⊢
  dyadic_interval [prec := 100]

theorem domain_bounds (b s : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    b-s ≠ 0 ∧ eps b s < 0 ∧ epsInterface b s < 0 ∧
    qVac s ∈ Set.Icc (2.0466875 : ℝ) 2.04671875 ∧
    qMat b s ∈ Set.Icc (2.1860 : ℝ) 2.1867 := by
  obtain ⟨her, hir⟩ := dielectric_intervals b s 3.01 3.012 hb hs (by norm_num)
  have he : eps b s ∈ Set.Icc (-1.970301 : ℝ) (-1.964423) :=
    ⟨le_trans (by norm_num) her.1, le_trans her.2 (by norm_num)⟩
  refine ⟨by linarith [hb.2, hs.1], lt_of_le_of_lt her.2 (by norm_num),
    lt_of_le_of_lt hir.2 (by norm_num), ?_, ?_⟩
  · dsimp [qVac]
    constructor <;> linarith [hs.1, hs.2]
  · unfold qMat
    rw [div_eq_mul_inv, show (64 : ℝ)⁻¹ = 0.015625 by norm_num]
    dyadic_interval [prec := 100]

/-- Exact polynomial interval certificates for spatial localization. -/
theorem profile_localization_bounds (b s : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ))
    (hs : s ∈ Set.Icc (3.01 : ℝ) 3.012) :
    8 * profile (qVac s) 7 ^ 2 ≤ (2 / 5 : ℝ) * profile (qVac s) 15 ^ 2 ∧
    8 * profile (qMat b s) 7 ^ 2 ≤ (2 / 5 : ℝ) * profile (qMat b s) 15 ^ 2 := by
  obtain ⟨_, _, _, hv, hm⟩ := domain_bounds b s hb hs
  rw [show (2 / 5 : ℝ) = 0.4 by norm_num]
  constructor <;>
    simp only [profile7, profile15, profilePolynomial7, profilePolynomial15, pow_two] <;>
    dyadic_interval [prec := 100]

@[fun_prop] theorem continuous_profile (n : ℕ) : Continuous (fun q : ℝ => profile q n) := by
  have h : ∀ n, Continuous (fun q : ℝ => profile q n) ∧
      Continuous (fun q : ℝ => profile q (n+1)) := by
    intro n
    induction n with
    | zero => constructor <;> dsimp [profile] <;> fun_prop
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      simp only [show n+1+1=n+2 by omega, profile_step]
      exact (continuous_id.mul ih.2).sub ih.1
  exact (h n).1

theorem characteristic_continuous (b : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ)) :
    ContinuousOn (characteristic b) (Set.Icc (3.01 : ℝ) 3.012) := by
  intro s hs
  obtain ⟨hd, he, hi, _, _⟩ := domain_bounds b s hb hs
  have hen : eps b s ≠ 0 := ne_of_lt he
  have hin : epsInterface b s ≠ 0 := ne_of_lt hi
  have hec : ContinuousAt (eps b) s := by unfold eps; fun_prop (disch := assumption)
  have hic : ContinuousAt (epsInterface b) s := by unfold epsInterface; fun_prop (disch := assumption)
  apply ContinuousAt.continuousWithinAt
  unfold characteristic leftResidual rightResidual interfaceCoupling qVac qMat
  fun_prop (disch := assumption)

theorem certified_root (b : ℝ)
    (hb : b ∈ Set.Icc (1999999 / 1000000 : ℝ) (2000001 / 1000000 : ℝ)) :
    ∃ s ∈ Set.Icc (3.01 : ℝ) 3.012, characteristic b s = 0 := by
  have h := intermediate_value_Icc (by norm_num : (3.01 : ℝ) ≤ 3.012)
    (characteristic_continuous b hb)
  exact h ⟨le_of_lt (lower_sign b hb), le_of_lt (upper_sign b hb)⟩

end VerifiedPhysics.MaxwellSlab
