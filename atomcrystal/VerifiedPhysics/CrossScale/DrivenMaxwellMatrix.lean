import VerifiedPhysics.Experiments.AtomisticMaxwellScattering

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace VerifiedPhysics.GratingExperiment
open MaxwellSlab

/-- The scalar stencil is exactly the independently specified finite curl
matrix, with the physical normal field restored from its Fourier scaling. -/
theorem driven_stencil_is_curl (b s J : ℝ) (f : Fields) (hf : DrivenResponse b s J f) :
    ∀ j : MagneticSite,
      (∑ i : ElectricSite, curlMatrix j i * electricVector f i) =
        s * magneticVector f j + (if j = 15 then J else 0) := by
  obtain ⟨_, _, _, _, hv0, hm0, hin, hv15, hm15⟩ := hf
  have hk (x : ℝ) : Real.sqrt 6 * (Real.sqrt 6 * x) = 6*x := by
    rw [← mul_assoc, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 6)]
  intro j
  fin_cases j
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [hv0]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 0 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 1 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 2 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 3 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 4 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 5 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 6 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 7 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 8 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 9 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 10 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 11 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 12 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 13 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [hv15]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [hm0]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 0 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 1 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 2 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 3 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 4 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 5 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 6 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 7 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 8 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 9 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 10 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 11 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 12 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [(hin 13 (by norm_num)).2]
  · norm_num [curlMatrix, electricVector, magneticVector, Fin.sum_univ_succ, hk]
    linarith [hm15]

theorem driven_stencil_is_curl_transpose (b s J : ℝ) (f : Fields) (hf : DrivenResponse b s J f) :
    ∀ i : ElectricSite,
      (∑ j : MagneticSite, curlMatrix j i * magneticVector f j) =
        electricVector f i + 3 * filling i * ionicVector f i := by
  obtain ⟨hn, he, hi, _, _, _, _, _, _⟩ := hf
  intro i
  fin_cases i
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 0 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 1 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 2 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 3 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 4 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 5 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 6 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 7 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 8 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 9 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 10 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 11 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 12 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 13 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 14 (by norm_num)).1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 0 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 1 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 2 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 3 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 4 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 5 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 6 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 7 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 8 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 9 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 10 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 11 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 12 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 13 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [(he 14 (by norm_num)).2.1]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 0 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 1 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 2 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 3 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 4 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 5 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 6 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 7 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 8 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 9 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 10 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 11 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 12 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 13 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 14 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 15 (by norm_num)).1
    nlinarith
  · norm_num [curlMatrix, electricVector, magneticVector, ionicVector, filling, Fin.sum_univ_succ]
    linarith [hi]

theorem driven_stencil_ionic_equations (b s J : ℝ) (f : Fields) (hf : DrivenResponse b s J f) :
    ∀ i : ElectricSite,
      filling i * ((b-s)*ionicVector f i-electricVector f i) = 0 := by
  obtain ⟨hn, he, _, hi, _, _, _, _, _⟩ := hf
  intro i
  fin_cases i
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 0 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 1 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 2 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 3 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 4 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 5 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 6 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 7 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 8 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 9 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 10 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 11 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 12 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 13 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
    linarith [(he 14 (by norm_num)).2.2]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 0 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 1 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 2 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 3 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 4 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 5 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 6 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 7 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 8 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 9 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 10 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 11 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 12 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 13 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 14 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    have h := congrArg (fun t : ℝ => Real.sqrt 6*t) (hn 15 (by norm_num)).2
    nlinarith
  · norm_num [electricVector, ionicVector, filling]
    linarith [hi]

/-- The driven stencil is precisely the primitive curl/Newton system, with
physical ionic displacements and the specified impressed magnetic source. -/
theorem driven_physical_equations (b s J : ℝ) (f : Fields)
    (hf : DrivenResponse b s J f) :
    (∀ j : MagneticSite, (∑ i : ElectricSite, curlMatrix j i * electricVector f i) =
      s * magneticVector f j + (if j = 15 then J else 0)) ∧
    (∀ i : ElectricSite, (∑ j : MagneticSite, curlMatrix j i * magneticVector f j) =
      electricVector f i + 3 * overlap i * (overlap i * ionicVector f i)) ∧
    (∀ i : ElectricSite, (b-s)*(overlap i * ionicVector f i) =
      overlap i * electricVector f i) := by
  refine ⟨driven_stencil_is_curl b s J f hf, ?_, ?_⟩
  · intro i
    rw [driven_stencil_is_curl_transpose b s J f hf i, ← overlap_sq i]
    ring
  · intro i
    have h := driven_stencil_ionic_equations b s J f hf i
    have hz : overlap i * ((b-s)*ionicVector f i-electricVector f i) = 0 := by
      rcases mul_eq_zero.mp h with hz | hz
      · have hg : overlap i = 0 := by simp [overlap, hz]
        rw [hg, zero_mul]
      · rw [hz, mul_zero]
    nlinarith

end VerifiedPhysics.GratingExperiment

