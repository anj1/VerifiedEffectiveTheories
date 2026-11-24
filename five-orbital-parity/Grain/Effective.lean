import Grain.Design
import Grain.RankOne

/-! The five-orbital reduction retains the kinetic reference. The largest
discarded row degree gives the diagonal shifts for two scalar Schur
comparisons. The two comparisons give energy endpoints from the input matrix. -/

namespace Grain

def referenceEnergy (levels : Fin 5 → ℤ) (c : Fin 3) : ℚ :=
  hamiltonian levels (4 + c.val) (referenceIndex c) (referenceIndex c)

def tailDiagonal (levels : Fin 5 → ℤ) (c : Fin 3) (i : Basis (4 + c.val)) : ℚ :=
  hamiltonian levels (4 + c.val) i i

def referenceCoupling (levels : Fin 5 → ℤ) (c : Fin 3) (i : Basis (4 + c.val)) : ℚ :=
  hamiltonian levels (4 + c.val) i (referenceIndex c)

def discardedDegree (c : Fin 3) (i : Basis (4 + c.val)) : ℕ :=
  if i = referenceIndex c then 0 else
    ((RankOne.tail (referenceIndex c)).filter fun j =>
      connects (codeOf i) (codeOf j)).card

/-- Each discarded hop has magnitude one in the declared energy unit. -/
def tailAllowance (c : Fin 3) : ℚ :=
  (Finset.univ.sup (discardedDegree c) : ℕ)

def comparisonMatrix (levels : Fin 5 → ℤ) (c : Fin 3) (shift : ℚ) :=
  RankOne.matrix (referenceIndex c) (referenceEnergy levels c)
    (fun i => tailDiagonal levels c i + shift) (referenceCoupling levels c)

def sectorLo (levels : Fin 5 → ℤ) (c : Fin 3) : ℚ :=
  RankOne.lowerEdge (referenceIndex c) (referenceEnergy levels c)
    (fun i => tailDiagonal levels c i - tailAllowance c) (referenceCoupling levels c)

def sectorHi (levels : Fin 5 → ℤ) (c : Fin 3) : ℚ :=
  RankOne.upperEdge (referenceIndex c) (referenceEnergy levels c)
    (fun i => tailDiagonal levels c i + tailAllowance c) (referenceCoupling levels c) (sectorLo levels c)

private def lowerDifference (levels : Fin 5 → ℤ) (c : Fin 3) (i j : Basis (4 + c.val)) : ℚ :=
  hamiltonian levels (4 + c.val) i j - comparisonMatrix levels c (-tailAllowance c) i j

private def upperDifference (levels : Fin 5 → ℤ) (c : Fin 3) (i j : Basis (4 + c.val)) : ℚ :=
  comparisonMatrix levels c (tailAllowance c) i j - hamiltonian levels (4 + c.val) i j

private theorem connects_self (a : Fin 243) : connects a a = false := by
  simp [connects, pairTransfer]

private theorem lowerDifference_entry (levels : Fin 5 → ℤ) (c : Fin 3) (i j : Basis (4 + c.val)) :
    lowerDifference levels c i j =
      if i = referenceIndex c ∨ j = referenceIndex c then 0
      else if i = j then tailAllowance c
      else if connects (codeOf i) (codeOf j) then -1 else 0 := by
  by_cases hi : i = referenceIndex c
  · subst i
    by_cases hj : j = referenceIndex c
    · subst j
      simp [lowerDifference, comparisonMatrix, RankOne.matrix, referenceEnergy]
    · simp [lowerDifference, comparisonMatrix, RankOne.matrix, hj, referenceCoupling,
        hamiltonian_symm levels (4 + c.val) (referenceIndex c) j]
  · by_cases hj : j = referenceIndex c
    · subst j
      simp [lowerDifference, comparisonMatrix, RankOne.matrix, hi, referenceCoupling]
    · by_cases hij : i = j
      · subst j
        simp [lowerDifference, comparisonMatrix, RankOne.matrix, tailDiagonal, hi]
      · simp [lowerDifference, comparisonMatrix, RankOne.matrix, hamiltonian, hi, hj, hij]

private theorem lowerDifference_rows (levels : Fin 5 → ℤ) (c : Fin 3) (i : Basis (4 + c.val)) :
    0 ≤ action (lowerDifference levels c) (fun _ => 1) i := by
  simp only [action, mul_one, lowerDifference_entry]
  by_cases hi : i = referenceIndex c
  · simp [hi]
  · simp only [hi, false_or]
    have hrow (j : Basis (4 + c.val)) :
        (if j = referenceIndex c then 0 else if i = j then tailAllowance c
          else if connects (codeOf i) (codeOf j) then -1 else 0) =
        (if i = j then tailAllowance c else 0) -
          (if j ∈ RankOne.tail (referenceIndex c) ∧ connects (codeOf i) (codeOf j)
            then 1 else 0) := by
      by_cases hij : i = j
      · subst j
        simp [hi, connects_self]
      · by_cases hj : j = referenceIndex c
        · simp [hi, hj, RankOne.tail]
        · cases connects (codeOf i) (codeOf j) <;>
            simp [hij, hj, RankOne.tail]
    simp_rw [hrow]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ i)]
    have hcount :
        (∑ j : Basis (4 + c.val),
          if j ∈ RankOne.tail (referenceIndex c) ∧ connects (codeOf i) (codeOf j)
            then (1 : ℚ) else 0) = (discardedDegree c i : ℚ) := by
      rw [← Finset.sum_filter]
      simp only [discardedDegree, hi, ite_false, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.cast_inj]
      congr 1
      ext j
      simp
    rw [hcount]
    exact sub_nonneg.mpr (by
      unfold tailAllowance
      exact_mod_cast (Finset.le_sup (f := discardedDegree c) (Finset.mem_univ i)))

private theorem lowerDifference_nonpos (levels : Fin 5 → ℤ) (c : Fin 3)
    (i j : Basis (4 + c.val)) (hne : i ≠ j) : lowerDifference levels c i j ≤ 0 := by
  rw [lowerDifference_entry]
  by_cases h : i = referenceIndex c ∨ j = referenceIndex c
  · simp [h]
  · cases connects (codeOf i) (codeOf j) <;> simp [h, hne]

private theorem lowerComparison (levels : Fin 5 → ℤ) (c : Fin 3) (x : Basis (4 + c.val) → ℝ) :
    form (comparisonMatrix levels c (-tailAllowance c)) x ≤
      form (hamiltonian levels (4 + c.val)) x := by
  have hsym i j : lowerDifference levels c i j = lowerDifference levels c j i := by
    simp only [lowerDifference_entry, or_comm, eq_comm (a := i) (b := j),
      connects_symm (codeOf i) (codeOf j)]
  have h := weighted_lower _ (fun _ => 1) 0 hsym
    (lowerDifference_nonpos levels c) (fun _ => by norm_num)
    (by simpa using lowerDifference_rows levels c) x
  unfold lowerDifference at h
  rw [form_sub] at h
  norm_num only [Rat.cast_zero, zero_mul] at h
  linarith

private theorem upperComparison (levels : Fin 5 → ℤ) (c : Fin 3) (x : Basis (4 + c.val) → ℝ) :
    form (hamiltonian levels (4 + c.val)) x ≤
      form (comparisonMatrix levels c (tailAllowance c)) x := by
  have h' (i j : Basis (4 + c.val)) :
      upperDifference levels c i j =
        if i = j then lowerDifference levels c i j else -lowerDifference levels c i j := by
    by_cases hij : i = j
    · subst j
      by_cases hi : i = referenceIndex c <;>
        simp [upperDifference, lowerDifference, comparisonMatrix, RankOne.matrix,
          referenceEnergy, tailDiagonal, hi]
    · simp only [ite_eq_right hij, upperDifference, lowerDifference, comparisonMatrix,
        RankOne.matrix, neg_sub]
  let y : Basis (4 + c.val) → ℝ := fun i => |x i|
  have hl : 0 ≤ form (lowerDifference levels c) y := by
    unfold lowerDifference
    rw [form_sub]
    exact sub_nonneg.mpr (lowerComparison levels c y)
  have ht : form (lowerDifference levels c) y ≤ form (upperDifference levels c) x := by
    unfold form
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    rw [h']
    by_cases hij : i = j
    · subst j
      simp [y]
    · simp only [ite_eq_right hij, Rat.cast_neg, y]
      have hs : ((lowerDifference levels c i j : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast lowerDifference_nonpos levels c i j hij
      have ha : -(x i * x j) ≤ |x i| * |x j| := by
        rw [← abs_mul]
        exact neg_le_abs _
      nlinarith only [mul_le_mul_of_nonpos_left ha hs]
  have hz := hl.trans ht
  unfold upperDifference at hz
  rw [form_sub] at hz
  linarith

theorem effective_bounds (levels : Fin 5 → ℤ) (c : Fin 3)
    (hgap : ∀ i ∈ RankOne.tail (referenceIndex c),
      0 < tailDiagonal levels c i - tailAllowance c - referenceEnergy levels c) :
    (sectorLo levels c : ℝ) ≤ sectorEnergy levels (4 + c.val) ∧
      sectorEnergy levels (4 + c.val) ≤ (sectorHi levels c : ℝ) := by
  have hallow : 0 ≤ tailAllowance c := by unfold tailAllowance; positivity
  have hd (i : Basis (4 + c.val)) (_ : i ∈ RankOne.tail (referenceIndex c)) :
      tailDiagonal levels c i - tailAllowance c ≤ tailDiagonal levels c i + tailAllowance c := by
    linarith
  exact RankOne.enclosure _ _ _ _ _ _ hgap hd
    (by simpa only [comparisonMatrix, sub_eq_add_neg] using lowerComparison levels c)
    (upperComparison levels c)

end Grain
