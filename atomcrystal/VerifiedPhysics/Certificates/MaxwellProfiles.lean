import VerifiedPhysics.Atomistic.MaxwellSlab

namespace VerifiedPhysics.MaxwellSlab

/-! Exact positive-coefficient polynomial witnesses for the finite transfer
recurrence. The coefficients are untrusted generated data; `ring` checks
every identity against the original Maxwell recurrence. -/

noncomputable def profilePolynomial7 (t : ℝ) : ℝ :=
  (1 + t * (28 + t * (126 + t * (210 + t * (165 + t * (66 + t * (13 + t * 1)))))))

theorem profile7 (q : ℝ) : profile q 7 = profilePolynomial7 (q - 2) := by
  norm_num [profile, profilePolynomial7]
  ring

noncomputable def profilePolynomial14 (t : ℝ) : ℝ :=
  (1 + t * (105 + t * (1820 + t * (12376 + t * (43758 + t * (92378 + t * (125970 + t * (116280 + t * (74613 + t * (33649 + t * (10626 + t * (2300 + t * (325 + t * (27 + t * 1))))))))))))))

theorem profile14 (q : ℝ) : profile q 14 = profilePolynomial14 (q - 2) := by
  norm_num [profile, profilePolynomial14]
  ring

noncomputable def profilePolynomial15 (t : ℝ) : ℝ :=
  (1 + t * (120 + t * (2380 + t * (18564 + t * (75582 + t * (184756 + t * (293930 + t * (319770 + t * (245157 + t * (134596 + t * (53130 + t * (14950 + t * (2925 + t * (378 + t * (29 + t * 1)))))))))))))))

theorem profile15 (q : ℝ) : profile q 15 = profilePolynomial15 (q - 2) := by
  norm_num [profile, profilePolynomial15]
  ring

end VerifiedPhysics.MaxwellSlab

