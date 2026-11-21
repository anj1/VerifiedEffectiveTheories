import Grain.Design

/-! Eliminate excited occupations in an arrowhead approximation. The two
arrowheads sandwich the primitive Hamiltonian in quadratic-form order.
The diagonal allowance covers all neglected excited-to-excited hops. -/

namespace Grain

def arrowhead (s : Spec) (n : ℕ) (shift : ℚ) (i j : Basis n) : ℚ :=
  if i = j then hamiltonian (spectrum s) n i i + (if reference n i then 0 else shift)
  else if reference n i || reference n j then hamiltonian (spectrum s) n i j else 0

theorem arrowhead_symm (s : Spec) (n : ℕ) (shift : ℚ) (i j : Basis n) :
    arrowhead s n shift i j = arrowhead s n shift j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [arrowhead, h, Ne.symm h, Bool.or_comm, hamiltonian_symm (spectrum s) n i j]

theorem arrowhead_nonpos (s : Spec) (n : ℕ) (shift : ℚ) (i j : Basis n) (h : i ≠ j) :
    arrowhead s n shift i j ≤ 0 := by
  simp only [arrowhead, ite_eq_right h]
  split
  · exact hamiltonian_nonpos (spectrum s) n i j h
  · exact le_rfl

/-- Coefficient from virtual pair hops out of the free reference occupation.
The sum is over one-hop destinations. Orbital energies are integers in the
chosen unit and the hopping amplitude is one. -/
def secondOrder (s : Spec) (n : ℕ) : ℚ :=
  ∑ i : Basis n, if reference n i then
    ∑ j : Basis n, if connects (codeOf i) (codeOf j) then
      (1 : ℚ) / (diagonal (spectrum s) (codeOf j) - diagonal (spectrum s) (codeOf i))
    else 0
  else 0

def referenceEnergy (s : Spec) (n : ℕ) : ℚ :=
  -(2 * (s.radius : ℚ) + 2000) - (if n = 6 then 3 else 2)

def center (s : Spec) (n : ℕ) : ℚ := referenceEnergy s n - secondOrder s n

def parityCenter (s : Spec) : ℚ := center s 5 - (center s 4 + center s 6) / 2

def sectorLo (s : Spec) (n : ℕ) : ℚ := center s n - sectorRadius
def sectorHi (s : Spec) (n : ℕ) : ℚ := center s n + sectorRadius

def refCode (n : ℕ) : Fin 243 := if n = 4 then 8 else if n = 5 then 17 else 26

/-- Solve the tail rows of a shifted arrowhead at the lower endpoint.
Isolated configurations use unit weight for the lower quadratic-form test. -/
def lowerWeight (s : Spec) (n : ℕ) (i : Basis n) : ℚ :=
  if connects (refCode n) (codeOf i) then
    1 / (arrowhead s n (-6) i i - sectorLo s n)
  else 1

/-- Solve the tail rows of the upper arrowhead. Isolated configurations
have zero trial amplitude. -/
def upperTrial (s : Spec) (n : ℕ) (i : Basis n) : ℚ :=
  if reference n i then 1
  else if connects (refCode n) (codeOf i) then
    1 / (arrowhead s n 6 i i - sectorHi s n)
  else 0

def lowerDifference (s : Spec) (n : ℕ) (i j : Basis n) : ℚ :=
  hamiltonian (spectrum s) n i j - arrowhead s n (-6) i j

def upperDifference (s : Spec) (n : ℕ) (i j : Basis n) : ℚ :=
  arrowhead s n 6 i j - hamiltonian (spectrum s) n i j

theorem lowerDifference_symm (s : Spec) (n : ℕ) (i j : Basis n) :
    lowerDifference s n i j = lowerDifference s n j i := by
  unfold lowerDifference
  rw [hamiltonian_symm _ _ i j, arrowhead_symm _ _ _ i j]

theorem upperDifference_symm (s : Spec) (n : ℕ) (i j : Basis n) :
    upperDifference s n i j = upperDifference s n j i := by
  unfold upperDifference
  rw [hamiltonian_symm _ _ i j, arrowhead_symm _ _ _ i j]

theorem lowerDifference_nonpos (s : Spec) (n : ℕ) (i j : Basis n) (h : i ≠ j) :
    lowerDifference s n i j ≤ 0 := by
  simp only [lowerDifference, arrowhead, ite_eq_right h]
  split
  · simp
  · simpa using hamiltonian_nonpos (spectrum s) n i j h

theorem upperDominates (s : Spec) (n : ℕ)
    (h : ∀ i : Basis n, 0 ≤ action (lowerDifference s n) (fun _ => 1) i)
    (x : Basis n → ℝ) : form (hamiltonian (spectrum s) n) x ≤ form (arrowhead s n 6) x := by
  have h' : ∀ i j, upperDifference s n i j =
      (if i = j then lowerDifference s n i j else -lowerDifference s n i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      by_cases href : reference n i <;>
        simp [upperDifference, lowerDifference, arrowhead, href]
    · simp only [upperDifference, lowerDifference, arrowhead, ite_eq_right hij, neg_sub]
  let y : Basis n → ℝ := fun i => |x i|
  have hl := weighted_lower (lowerDifference s n) (fun _ => 1) 0
    (lowerDifference_symm s n) (lowerDifference_nonpos s n)
    (fun _ => by norm_num) (by simpa using h) y
  have ht : form (lowerDifference s n) y ≤ form (upperDifference s n) x := by
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
      have hs : ((lowerDifference s n i j : ℚ) : ℝ) ≤ 0 := by
        exact_mod_cast lowerDifference_nonpos s n i j hij
      have ha : -(x i * x j) ≤ |x i| * |x j| := by
        rw [← abs_mul]
        exact neg_le_abs _
      nlinarith only [mul_le_mul_of_nonpos_left ha hs]
  have hz : (0 : ℝ) ≤ form (upperDifference s n) x :=
    (by simpa using hl : (0 : ℝ) ≤ form (lowerDifference s n) y).trans ht
  unfold upperDifference at hz
  rw [form_sub] at hz
  linarith

theorem effective_bounds (s : Spec) (n : ℕ)
    (hgap : ∀ i : Basis n, 0 ≤ action (lowerDifference s n) (fun _ => 1) i)
    (hw : ∀ i, 0 < lowerWeight s n i)
    (hl : ∀ i, sectorLo s n * lowerWeight s n i ≤
      action (arrowhead s n (-6)) (lowerWeight s n) i)
    (htrial : 0 < rationalNormSq (upperTrial s n))
    (hu : rayleighNumerator (arrowhead s n 6) (upperTrial s n) ≤
      sectorHi s n * rationalNormSq (upperTrial s n)) :
    (sectorLo s n : ℝ) ≤ sectorEnergy (spectrum s) n ∧
      sectorEnergy (spectrum s) n ≤ (sectorHi s n : ℝ) := by
  apply ground_bounds
  · intro x
    have hr := weighted_lower _ _ _ (arrowhead_symm s n (-6))
      (arrowhead_nonpos s n (-6)) hw hl x
    have hd := weighted_lower (lowerDifference s n) (fun _ => 1) 0
      (lowerDifference_symm s n) (lowerDifference_nonpos s n)
      (fun _ => by norm_num) (by simpa using hgap) x
    unfold lowerDifference at hd
    rw [form_sub] at hd
    norm_num only [Rat.cast_zero, zero_mul] at hd
    linarith
  · obtain ⟨e, ⟨x, hx, rfl⟩, he⟩ := normalized_trial _ _ htrial _ hu
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    exact (div_le_div_of_nonneg_right (upperDominates s n hgap x) hx.le).trans he

end Grain
