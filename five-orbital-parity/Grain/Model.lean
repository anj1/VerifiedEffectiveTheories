import Grain.Energy

/-! The reduced BCS Hamiltonian in the occupation basis, at unit bare coupling.
Each orbital holds zero electrons, one blocked electron, or a pair.
Spin labels of blocked electrons give identical copies of the same block.
The paired states use products of even fermion operators on distinct orbitals,
so the off-diagonal amplitude of a pair transfer is uniformly negative. -/

namespace Grain

def occupation (code : Fin 243) (orbital : Fin 5) : ℕ :=
  code.val / 3 ^ orbital.val % 3

def configurations (n : ℕ) : Array (Fin 243) :=
  ((List.finRange 243).filter fun code => (∑ k : Fin 5, occupation code k) == n).toArray

abbrev Basis (n : ℕ) := Fin (configurations n).size

def codeOf {n : ℕ} (i : Basis n) : Fin 243 := (configurations n)[i]

def pairCount (c : Fin 243) : ℕ :=
  ∑ k : Fin 5, if occupation c k = 2 then 1 else 0

def blocked (c : Fin 243) : ℕ :=
  ∑ k : Fin 5, if occupation c k = 1 then 2 ^ k.val else 0

def pairTransfer (a b : Fin 243) : Bool :=
  blocked a == blocked b &&
    (∑ k : Fin 5, if occupation a k = occupation b k then 0 else 1 : ℕ) == 2

def connects (a b : Fin 243) : Bool := pairTransfer (min a b) (max a b)

theorem connects_symm (a b : Fin 243) : connects a b = connects b a := by
  rw [connects, connects, min_comm a b, max_comm a b]

def diagonal (orbitalEnergy : Fin 5 → ℤ) (c : Fin 243) : ℤ :=
  (∑ k : Fin 5, (occupation c k : ℤ) * orbitalEnergy k) - pairCount c

def hamiltonian (orbitalEnergy : Fin 5 → ℤ) (n : ℕ) (i j : Basis n) : ℚ :=
  if i = j then diagonal orbitalEnergy (codeOf i)
  else if connects (codeOf i) (codeOf j) then -1 else 0

theorem hamiltonian_symm (s : Fin 5 → ℤ) (n : ℕ) (i j : Basis n) :
    hamiltonian s n i j = hamiltonian s n j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [hamiltonian, h, Ne.symm h, connects_symm (codeOf i) (codeOf j)]

theorem hamiltonian_nonpos (s : Fin 5 → ℤ) (n : ℕ) (i j : Basis n) (h : i ≠ j) :
    hamiltonian s n i j ≤ 0 := by
  simp only [hamiltonian, ite_eq_right h]
  split <;> norm_num

noncomputable def sectorEnergy (s : Fin 5 → ℤ) (n : ℕ) : ℝ :=
  ground (hamiltonian s n)

noncomputable def parity (s : Fin 5 → ℤ) : ℝ :=
  sectorEnergy s 5 - (sectorEnergy s 4 + sectorEnergy s 6) / 2

/-- Freeze the outer occupations and retain the three central occupations 0, 1, 2.
The common outer energy is an arbitrary offset. -/
def frozenBareParity (outer offset : ℚ) : ℚ :=
  (outer + offset) - (outer + (outer + 2 * offset - 1)) / 2

theorem frozenBareParity_eq (outer offset : ℚ) : frozenBareParity outer offset = 1 / 2 := by
  unfold frozenBareParity
  ring

end Grain
