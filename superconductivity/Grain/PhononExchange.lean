import Grain.PhononVariational

/-! The local virtual exchange calculation in a site-ordered fermion basis.
The four modes are low-up, low-down, high-up, high-down. -/

namespace Grain.Phonon

def occupied (state : Fin 16) (mode : Fin 4) : Bool := state.val.testBit mode.val

def electronHop (source destination between : Fin 4) (state target : Fin 16) : ℤ :=
  if occupied state source != occupied state destination then
    if target.val = state.val ^^^ (2 ^ source.val + 2 ^ destination.val) then
      if occupied state between then -1 else 1
    else 0
  else 0

def bondVertex (i j : Fin 16) : ℤ :=
  electronHop 0 2 1 i j + electronHop 1 3 2 i j

def bondSquare (i j : Fin 16) : ℤ := ∑ k : Fin 16, bondVertex i k * bondVertex k j

def bondDegree (i : Fin 16) : ℤ :=
  (if occupied i 0 != occupied i 2 then 1 else 0) +
    (if occupied i 1 != occupied i 3 then 1 else 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- The square of the one-electron bond vertex. Configurations 3 and 12
are the two pair locations. Configurations 6 and 9 are the opposite-spin
singly occupied states. -/
theorem bond_square_entries (i j : Fin 16) :
    bondSquare i j =
      if i = j then bondDegree i
      else if (i = 3 ∧ j = 12) ∨ (i = 12 ∧ j = 3) then 2
      else if (i = 6 ∧ j = 9) ∨ (i = 9 ∧ j = 6) then -2
      else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem bond_vertex_symm (i j : Fin 16) : bondVertex i j = bondVertex j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- There is no pair hop in a single vertex. Eliminating the harmonic
coordinate gives an attractive pair hop from the product of two vertices. -/
theorem generated_pair_transfer (ω a : ℝ) (hω : 0 < ω) (ha : a ≠ 0) :
    bondVertex 3 12 = 0 ∧
      -(ω * a^2) * (bondSquare 3 12 : ℝ) = -(2 * ω * a^2) ∧
      -(ω * a^2) * (bondSquare 3 12 : ℝ) < 0 := by
  have hs : bondSquare 3 12 = 2 := by decide +kernel
  refine ⟨by decide +kernel, ?_, ?_⟩
  · rw [hs]
    push_cast
    ring
  · rw [hs]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hω (sq_pos_of_ne_zero ha))) (by norm_num)

end Grain.Phonon
