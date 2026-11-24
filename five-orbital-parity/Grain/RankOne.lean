import Grain.Energy

/-! Scalar Schur elimination and energy enclosures for one retained state. -/

namespace Grain.RankOne

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tail (head : ι) : Finset ι := Finset.univ.erase head

def matrix (head : ι) (a : ℚ) (d b : ι → ℚ) (i j : ι) : ℚ :=
  if i = head then if j = head then a else b j
  else if j = head then b i else if i = j then d i else 0

def selfEnergy (head : ι) (d b : ι → ℚ) (z : ℚ) : ℚ :=
  ∑ i ∈ tail head, b i ^ 2 / (d i - z)

private theorem splitSum {M : Type} [AddCommMonoid M] (head : ι) (f : ι → M) :
    (∑ i, f i) = f head + ∑ i ∈ tail head, f i := by
  rw [add_comm, tail, Finset.sum_erase_add _ _ (Finset.mem_univ _)]

/-- Eliminating a diagonal discarded block gives a scalar Schur complement.
The last term vanishes for the unique lift of the retained amplitude. -/
theorem shifted_form (head : ι) (a z : ℚ) (d b : ι → ℚ)
    (hp : ∀ i ∈ tail head, 0 < d i - z) (x : ι → ℝ) :
    form (matrix head a d b) x - (z : ℝ) * normSq x =
      ((a - z - selfEnergy head d b z : ℚ) : ℝ) * x head ^ 2 +
        ∑ i ∈ tail head, ((d i : ℝ) - z) *
          (x i + (b i : ℝ) / ((d i : ℝ) - z) * x head) ^ 2 := by
  classical
  have hne (i : ι) (hi : i ∈ tail head) : i ≠ head := (Finset.mem_erase.mp hi).1
  have hrow (i : ι) (hi : i ∈ tail head) :
      (∑ j, (matrix head a d b i j : ℝ) * (x i * x j)) =
        (b i : ℝ) * (x i * x head) + (d i : ℝ) * x i ^ 2 := by
    rw [splitSum head]
    simp only [matrix, ite_eq_right (hne i hi), ite_true]
    congr 1
    rw [Finset.sum_eq_single_of_mem i hi]
    · simp [hne i hi, pow_two]
    · intro j hj hji
      simp [hne j hj, Ne.symm hji]
  have hhead :
      (∑ j, (matrix head a d b head j : ℝ) * (x head * x j)) =
        (a : ℝ) * x head ^ 2 + ∑ j ∈ tail head, (b j : ℝ) * (x head * x j) := by
    rw [splitSum head]
    simp only [matrix, ite_true, pow_two]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by simp [hne j hj]
  unfold form normSq
  rw [splitSum head, hhead, splitSum head (fun i => x i ^ 2)]
  rw [Finset.sum_congr rfl hrow]
  simp only [selfEnergy, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_pow]
  have hterm (i : ι) (hi : i ∈ tail head) :
      ((d i : ℝ) - z) * (x i + (b i : ℝ) / ((d i : ℝ) - z) * x head) ^ 2 =
        (b i : ℝ) ^ 2 / ((d i : ℝ) - z) * x head ^ 2 +
          ((b i : ℝ) * (x head * x i) + ((b i : ℝ) * (x i * x head) +
            (d i : ℝ) * x i ^ 2)) - (z : ℝ) * x i ^ 2 := by
    have hn : (d i : ℝ) - z ≠ 0 := by exact_mod_cast (hp i hi).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  rw [mul_add, Finset.mul_sum]
  ring

theorem selfEnergy_nonneg (head : ι) (d b : ι → ℚ) (z : ℚ)
    (hp : ∀ i ∈ tail head, 0 < d i - z) :
    0 ≤ selfEnergy head d b z := by
  exact Finset.sum_nonneg fun i hi => div_nonneg (sq_nonneg _) (hp i hi).le

theorem selfEnergy_mono (head : ι) (d b : ι → ℚ) {l u : ℚ}
    (hlu : l ≤ u) (hp : ∀ i ∈ tail head, 0 < d i - u) :
    selfEnergy head d b l ≤ selfEnergy head d b u := by
  exact Finset.sum_le_sum fun i hi =>
    div_le_div_of_nonneg_left (sq_nonneg _) (hp i hi) (by linarith)

theorem selfEnergy_of_diag_le (head : ι) (d₁ d₂ b : ι → ℚ) (z : ℚ)
    (hd : ∀ i ∈ tail head, d₁ i ≤ d₂ i)
    (hp : ∀ i ∈ tail head, 0 < d₁ i - z) :
    selfEnergy head d₂ b z ≤ selfEnergy head d₁ b z := by
  exact Finset.sum_le_sum fun i hi =>
    div_le_div_of_nonneg_left (sq_nonneg _) (hp i hi) (by linarith [hd i hi])

/-- Evaluate the lower comparison at the bare energy. The correction can
only decrease as the energy falls, so this first step is a lower bound. -/
def lowerEdge (head : ι) (a : ℚ) (d b : ι → ℚ) : ℚ :=
  a - selfEnergy head d b a

/-- Evaluate the upper comparison at the lower edge. The correction can
only increase as the energy rises, so this step gives an upper bound. -/
def upperEdge (head : ι) (a : ℚ) (d b : ι → ℚ) (lo : ℚ) : ℚ :=
  a - selfEnergy head d b lo

theorem enclosure (H : ι → ι → ℚ) (head : ι) (a : ℚ) (lowerDiag upperDiag b : ι → ℚ)
    (hp : ∀ i ∈ tail head, 0 < lowerDiag i - a)
    (hd : ∀ i ∈ tail head, lowerDiag i ≤ upperDiag i)
    (hlo : ∀ x, form (matrix head a lowerDiag b) x ≤ form H x)
    (hhi : ∀ x, form H x ≤ form (matrix head a upperDiag b) x) :
    let l := lowerEdge head a lowerDiag b
    let u := upperEdge head a upperDiag b l
    (l : ℝ) ≤ ground H ∧ ground H ≤ (u : ℝ) := by
  intro l u
  have hla : l ≤ a := sub_le_self _ (selfEnergy_nonneg head lowerDiag b a hp)
  have hpl (i : ι) (hi : i ∈ tail head) : 0 < lowerDiag i - l := by linarith [hp i hi]
  have hpl' (i : ι) (hi : i ∈ tail head) : 0 < upperDiag i - l := by
    linarith [hd i hi, hpl i hi]
  have hua : u ≤ a := sub_le_self _ (selfEnergy_nonneg head upperDiag b l hpl')
  have hlu : l ≤ u := by
    have h₁ := selfEnergy_mono head lowerDiag b hla hp
    have h₂ := selfEnergy_of_diag_le head lowerDiag upperDiag b l hd hpl
    exact sub_le_sub_left (h₂.trans h₁) a
  have hpu (i : ι) (hi : i ∈ tail head) : 0 < upperDiag i - u := by
    linarith [hd i hi, hp i hi]
  apply ground_bounds H l u
  · intro x
    have hs := shifted_form head a l lowerDiag b hpl x
    have hc : 0 ≤ a - l - selfEnergy head lowerDiag b l := by
      have hm := selfEnergy_mono head lowerDiag b hla hp
      rw [show a - l = selfEnergy head lowerDiag b a by
        change a - (a - _) = _
        ring]
      exact sub_nonneg.mpr hm
    have hn : 0 ≤ ((a - l - selfEnergy head lowerDiag b l : ℚ) : ℝ) * x head ^ 2 :=
      mul_nonneg (by exact_mod_cast hc) (sq_nonneg _)
    have ht : 0 ≤ ∑ i ∈ tail head, ((lowerDiag i : ℝ) - l) *
        (x i + (b i : ℝ) / ((lowerDiag i : ℝ) - l) * x head) ^ 2 :=
      Finset.sum_nonneg fun i hi => mul_nonneg (by exact_mod_cast (hpl i hi).le) (sq_nonneg _)
    linarith [hlo x]
  · let x : ι → ℝ := fun i => if i = head then 1 else -(b i : ℝ) / ((upperDiag i : ℝ) - u)
    have hx : x head = 1 := by simp [x]
    have hn : 0 < normSq x := by
      unfold normSq
      rw [splitSum head, hx]
      have ht : 0 ≤ ∑ i ∈ tail head, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      positivity
    have hz : (∑ i ∈ tail head, ((upperDiag i : ℝ) - u) *
        (x i + (b i : ℝ) / ((upperDiag i : ℝ) - u) * x head) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [x, (Finset.mem_erase.mp hi).1, neg_div]
    have hc : a - u - selfEnergy head upperDiag b u ≤ 0 := by
      have hm := selfEnergy_mono head upperDiag b hlu hpu
      rw [show a - u = selfEnergy head upperDiag b l by
        change a - (a - _) = _
        ring]
      exact sub_nonpos.mpr hm
    have hc' : ((a - u - selfEnergy head upperDiag b u : ℚ) : ℝ) ≤ 0 := by exact_mod_cast hc
    have hs := shifted_form head a u upperDiag b hpu x
    rw [hz, hx, one_pow, mul_one, add_zero] at hs
    exact ⟨_, ⟨x, hn, rfl⟩, (div_le_iff₀ hn).2 (by linarith [hhi x])⟩

end Grain.RankOne
