import Grain.Prediction

/-! Reindex the second-order sum by the source and destination of a pair.
The finite checks below concern occupation codes only. The energy
denominators and parity cancellation are proved symbolically. -/

namespace Grain

namespace ParityCancellation

/-- The central orbital is `none`. The other orbitals are indexed by the
filled and empty levels of the free reference. -/
abbrev Orbital (L U : Type) := Option (L ⊕ U)

private def referenceOccupation {L U : Type} (central : Fin 3) : Orbital L U → Fin 3
  | none => central
  | some (.inl _) => 2
  | some (.inr _) => 0

private def legalHop {L U : Type} (central : Fin 3) (hop : Orbital L U × Orbital L U) : Bool :=
  referenceOccupation central hop.1 == 2 && referenceOccupation central hop.2 == 0

private def orbitalEnergy {L U : Type} (lower : L → ℚ) (upper : U → ℚ) : Orbital L U → ℚ
  | none => 0
  | some (.inl i) => lower i
  | some (.inr j) => upper j

private def hopCost {L U : Type} (g : ℚ) (lower : L → ℚ) (upper : U → ℚ)
    (hop : Orbital L U × Orbital L U) : ℚ :=
  (g ^ 2 / 2) * (1 / (orbitalEnergy lower upper hop.2 - orbitalEnergy lower upper hop.1))

/-- The positive sum subtracted from a reference energy at second order. -/
def virtualHopSum {L U : Type} [Fintype L] [Fintype U] (g : ℚ)
    (lower : L → ℚ) (upper : U → ℚ) (central : Fin 3) : ℚ :=
  ∑ hop : Orbital L U × Orbital L U,
    if legalHop central hop then hopCost g lower upper hop else 0

private theorem virtualHopSum_split {L U : Type} [Fintype L] [Fintype U] (g : ℚ)
    (lower : L → ℚ) (upper : U → ℚ) (central : Fin 3) :
    virtualHopSum g lower upper central =
      (∑ i : L, ∑ j : U, hopCost g lower upper (some (.inl i), some (.inr j))) +
      (if central = 0 then ∑ i : L, hopCost g lower upper (some (.inl i), none) else 0) +
      (if central = 2 then ∑ j : U, hopCost g lower upper (none, some (.inr j)) else 0) := by
  fin_cases central <;>
    simp [virtualHopSum, Fintype.sum_prod_type, Fintype.sum_option, Fintype.sum_sum_type,
      legalHop, referenceOccupation, Finset.sum_add_distrib] <;> abel

/-- Every filled-to-empty hop has the same denominator in all three
sectors. Only hops involving the central orbital survive in parity.
The physical regime has negative `lower` and positive `upper` energies. -/
theorem secondOrder_parity {L U : Type} [Fintype L] [Fintype U] (g : ℚ)
    (lower : L → ℚ) (upper : U → ℚ) :
    (virtualHopSum g lower upper 0 + virtualHopSum g lower upper 2) / 2 -
        virtualHopSum g lower upper 1 =
      (g ^ 2 / 4) * ((∑ i : L, 1 / (-lower i)) + ∑ j : U, 1 / upper j) := by
  simp only [virtualHopSum_split, Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero,
    hopCost, orbitalEnergy, sub_zero, zero_sub, ← Finset.mul_sum]
  ring

private def orbitalIndex : Orbital (Fin 2) (Fin 2) → Fin 5
  | none => 2
  | some (.inl i) => ![0, 1] i
  | some (.inr j) => ![3, 4] j

private abbrev FiveHop := Orbital (Fin 2) (Fin 2) × Orbital (Fin 2) (Fin 2)

/-- The index of the occupation obtained by moving the two trits at the
endpoints. Its value will only be used on legal hops. -/
private def afterHopIndex (c : Fin 3) (hop : FiveHop) : Basis (4 + c.val) :=
  let movedCode := Fin.ofNat 243
    ((refCode (4 + c.val)).val - 2 * 3 ^ (orbitalIndex hop.1).val +
      2 * 3 ^ (orbitalIndex hop.2).val)
  let basis := configurations (4 + c.val)
  ⟨basis.idxOf movedCode % basis.size, Nat.mod_lt _ (referenceIndex c).isLt.pos⟩

private def legalHops (c : Fin 3) : Finset FiveHop :=
  Finset.univ.filter fun hop => legalHop c hop

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem encodedNeighbors (c : Fin 3) :
    (legalHops c).image (afterHopIndex c) =
      Finset.univ.filter fun j => connects (codeOf (referenceIndex c)) (codeOf j) := by
  fin_cases c <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem encodedHop_injective (c : Fin 3) :
    Set.InjOn (afterHopIndex c) (legalHops c : Set FiveHop) := by
  rw [← Finset.card_image_iff]
  fin_cases c <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem encodedHop_changes (c : Fin 3) (hop : FiveHop) (h : hop ∈ legalHops c) :
    let a := codeOf (referenceIndex c)
    let b := codeOf (afterHopIndex c hop)
    pairCount b = pairCount a ∧
      ∀ k : Fin 5, (occupation b k : ℤ) - occupation a k =
        (if k = orbitalIndex hop.2 then 2 else 0) - (if k = orbitalIndex hop.1 then 2 else 0) := by
  revert hop h
  fin_cases c <;> decide +kernel

private theorem hop_gap (levels : Fin 5 → ℤ) (c : Fin 3) (hop : FiveHop)
    (h : hop ∈ legalHops c) :
    diagonal levels (codeOf (afterHopIndex c hop)) - diagonal levels (codeOf (referenceIndex c)) =
      2 * (levels (orbitalIndex hop.2) - levels (orbitalIndex hop.1)) := by
  obtain ⟨hpairs, hoccupation⟩ := encodedHop_changes c hop h
  unfold diagonal
  rw [hpairs, sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul, hoccupation, sub_mul, ite_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp
  ring

private def lowerLevels (levels : Fin 5 → ℤ) (i : Fin 2) : ℚ :=
  levels (orbitalIndex (some (.inl i)))

private def upperLevels (levels : Fin 5 → ℤ) (j : Fin 2) : ℚ :=
  levels (orbitalIndex (some (.inr j)))

private theorem orbitalEnergy_eq (levels : Fin 5 → ℤ) (h : levels 2 = 0)
    (o : Orbital (Fin 2) (Fin 2)) :
    orbitalEnergy (lowerLevels levels) (upperLevels levels) o = (levels (orbitalIndex o) : ℚ) := by
  rcases o with _ | (i | j)
  · simp [orbitalEnergy, orbitalIndex, h]
  · rfl
  · rfl

private theorem secondOrder_eq_virtualHopSum (levels : Fin 5 → ℤ) (h : levels 2 = 0)
    (c : Fin 3) :
    secondOrder levels c = virtualHopSum 1 (lowerLevels levels) (upperLevels levels) c := by
  let head := referenceIndex c
  let neighbors := Finset.univ.filter fun j : Basis (4 + c.val) =>
    connects (codeOf head) (codeOf j)
  have hsub : neighbors ⊆ RankOne.tail head := by
    intro j hj
    have hconn := (Finset.mem_filter.mp hj).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    simp [connects, pairTransfer] at hconn
  unfold secondOrder RankOne.selfEnergy
  rw [← Finset.sum_subset hsub (f := fun i =>
    referenceCoupling levels c i ^ 2 / (tailDiagonal levels c i - referenceEnergy levels c))
    (by
      intro i hi hn
      have hne := (Finset.mem_erase.mp hi).1
      have hconn : connects (codeOf head) (codeOf i) = false := by
        simpa [neighbors] using hn
      simp [referenceCoupling, hamiltonian, hne, connects_symm (codeOf i) (codeOf head), head,
        show connects (codeOf (referenceIndex c)) (codeOf i) =
          false from hconn])]
  change (∑ j ∈ neighbors, _) = _
  rw [show neighbors = (legalHops c).image (afterHopIndex c) from (encodedNeighbors c).symm,
    Finset.sum_image (encodedHop_injective c)]
  unfold virtualHopSum
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro hop hh
  have hmem := (Finset.mem_image_of_mem (afterHopIndex c) hh)
  rw [encodedNeighbors c] at hmem
  have hconn := (Finset.mem_filter.mp hmem).2
  have hne : afterHopIndex c hop ≠ referenceIndex c := (Finset.mem_erase.mp (hsub hmem)).1
  have gap := congrArg (fun x : ℤ => (x : ℚ)) (hop_gap levels c hop hh)
  push_cast at gap
  simp only [tailDiagonal, referenceEnergy, hamiltonian, ite_true, referenceCoupling,
    ite_eq_right hne, connects_symm (codeOf (afterHopIndex c hop)) (codeOf (referenceIndex c)),
    hconn, ite_true, neg_one_sq]
  rw [gap]
  simp [hopCost, orbitalEnergy_eq levels h, div_eq_mul_inv, mul_comm]

private theorem reference_diagonal (levels : Fin 5 → ℤ) (c : Fin 3) :
    referenceEnergy levels c =
      2 * (levels 0 : ℚ) + 2 * (levels 1 : ℚ) + (c.val : ℚ) * (levels 2 : ℚ) -
        (if c = 2 then 3 else 2) := by
  have hocc (k : Fin 5) :
      occupation (codeOf (referenceIndex c)) k = filling (4 + c.val) k := by
    revert k
    fin_cases c <;> decide +kernel
  have hpairs : pairCount (codeOf (referenceIndex c)) = if c = 2 then 3 else 2 := by
    fin_cases c <;> decide +kernel
  simp only [referenceEnergy, hamiltonian, ite_true, diagonal, hocc, hpairs,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases c <;> norm_num [filling] <;> ring

theorem bare_parity (levels : Fin 5 → ℤ) : bareParity levels = 1 / 2 := by
  unfold bareParity
  rw [reference_diagonal, reference_diagonal, reference_diagonal]
  norm_num
  ring

theorem parity_center_from_hops (levels : Fin 5 → ℤ) (h : levels 2 = 0) :
    parityCenter levels = 1 / 2 +
      (1 / 4) * ((∑ i : Fin 2, 1 / (-lowerLevels levels i)) +
        ∑ j : Fin 2, 1 / upperLevels levels j) := by
  have he := secondOrder_parity 1 (lowerLevels levels) (upperLevels levels)
  rw [← secondOrder_eq_virtualHopSum levels h, ← secondOrder_eq_virtualHopSum levels h,
    ← secondOrder_eq_virtualHopSum levels h] at he
  have hb := bare_parity levels
  unfold parityCenter center bareParity at *
  linarith

/-- The symmetric spectrum leaves one reciprocal contribution per shell. -/
theorem shell_center (spacing radius : ℤ) :
    parityCenter (symmetricSpectrum spacing radius) =
      1 / 2 + (1 / (spacing : ℚ) + 1 / (radius : ℚ)) / 2 := by
  rw [parity_center_from_hops _ (by rfl)]
  norm_num [symmetricSpectrum, lowerLevels, upperLevels, orbitalIndex, Fin.sum_univ_two]
  ring

theorem shell_center_decreases (spacing : ℤ) {r₁ r₂ : ℤ} (h₁ : 0 < r₁) (h₂ : r₁ < r₂) :
    parityCenter (symmetricSpectrum spacing r₂) <
      parityCenter (symmetricSpectrum spacing r₁) := by
  rw [shell_center, shell_center]
  have hp : (0 : ℚ) < r₁ := by exact_mod_cast h₁
  have hr : (r₁ : ℚ) < r₂ := by exact_mod_cast h₂
  linarith [one_div_lt_one_div_of_lt hp hr]

theorem contrast_center_from_hops : contrastCenter = 1 / 9000 := by
  unfold contrastCenter spectrum
  rw [shell_center, shell_center]
  norm_num [Spec.radius]

end ParityCancellation

end Grain
