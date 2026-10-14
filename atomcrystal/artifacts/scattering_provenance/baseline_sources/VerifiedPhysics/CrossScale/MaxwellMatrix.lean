import VerifiedPhysics.Atomistic.MaxwellHamiltonian

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace VerifiedPhysics.MaxwellSlab

/-- The scalar stencil is exactly the independently specified finite curl
matrix, with the physical normal field restored from its Fourier scaling. -/
theorem stencil_is_curl (b s : ℝ) (f : Fields) (hf : MaxwellIonMode b s f) :
    ∀ j : MagneticSite,
      (∑ i : ElectricSite, curlMatrix j i * electricVector f i) =
        s * magneticVector f j := by
  obtain ⟨_, _, _, _, _, hv0, hm0, hin, hv15, hm15⟩ := hf
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

theorem stencil_is_curl_transpose (b s : ℝ) (f : Fields) (hf : MaxwellIonMode b s f) :
    ∀ i : ElectricSite,
      (∑ j : MagneticSite, curlMatrix j i * magneticVector f j) =
        electricVector f i + 3 * filling i * ionicVector f i := by
  obtain ⟨_, hn, he, hi, _, _, _, _, _, _⟩ := hf
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

theorem stencil_ionic_equations (b s : ℝ) (f : Fields) (hf : MaxwellIonMode b s f) :
    ∀ i : ElectricSite,
      filling i * ((b-s)*ionicVector f i-electricVector f i) = 0 := by
  obtain ⟨_, hn, he, _, hi, _, _, _, _, _⟩ := hf
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

/-- An eigenmode of the finite Maxwell-ion operator in physical ionic
coordinates. `u` is an actual ionic displacement amplitude, with reduced
mass 3 and charge 3; the interface overlap is explicit. -/
def AtomisticMaxwellEigenmode (b s : ℝ) (E : ElectricSite → ℝ)
    (H : MagneticSite → ℝ) (u : ElectricSite → ℝ) : Prop :=
  0 < H 15 ^ 2 + H 31 ^ 2 ∧
  (∀ j, (∑ i, curlMatrix j i * E i) = s * H j) ∧
  (∀ i, (∑ j, curlMatrix j i * H j) = E i + 3 * overlap i * u i) ∧
  (∀ i, (b-s)*u i = overlap i*E i)

theorem stencil_physical_eigenmode (b s : ℝ) (f : Fields) (hf : MaxwellIonMode b s f) :
    AtomisticMaxwellEigenmode b s (electricVector f) (magneticVector f)
      (fun i => overlap i * ionicVector f i) := by
  refine ⟨?_, stencil_is_curl b s f hf, ?_, ?_⟩
  · simpa [magneticVector] using hf.1
  · intro i
    rw [stencil_is_curl_transpose b s f hf i, ← overlap_sq i]
    ring
  · intro i
    have h := stencil_ionic_equations b s f hf i
    have hz : overlap i * ((b-s)*ionicVector f i-electricVector f i) = 0 := by
      rcases mul_eq_zero.mp h with hz | hz
      · have hg : overlap i = 0 := by simp [overlap, hz]
        rw [hg, zero_mul]
      · rw [hz, mul_zero]
    nlinarith

end VerifiedPhysics.MaxwellSlab
