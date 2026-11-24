import Grain.Model

namespace Grain

inductive Spec where
  | near
  | far
  deriving DecidableEq

def Spec.radius : Spec → ℤ
  | .near => 3000
  | .far => 9000

def symmetricSpectrum (spacing radius : ℤ) : Fin 5 → ℤ :=
  ![-radius, -spacing, 0, spacing, radius]

def spectrum (s : Spec) : Fin 5 → ℤ := symmetricSpectrum 1000 s.radius

/-- Fill the orbitals in increasing energy order, with two spin slots per orbital. -/
def filling (n : ℕ) (k : Fin 5) : ℕ := min 2 (n - 2 * k.val)

def refCode (n : ℕ) : Fin 243 :=
  Fin.ofNat 243 (∑ k : Fin 5, filling n k * 3 ^ k.val)

/-- Basis index of the kinetic reference in each parity sector. -/
def referenceIndex (c : Fin 3) : Basis (4 + c.val) :=
  ⟨(configurations (4 + c.val)).idxOf (refCode (4 + c.val)), by
    fin_cases c <;> decide +kernel⟩

end Grain
