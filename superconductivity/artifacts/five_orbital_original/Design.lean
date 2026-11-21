import Grain.Model

namespace Grain

inductive Spec where
  | near
  | far
  deriving DecidableEq

def Spec.radius : Spec → ℤ
  | .near => 3000
  | .far => 9000

def spectrum (s : Spec) : Fin 5 → ℤ :=
  ![-s.radius, -1000, 0, 1000, s.radius]

/-- Ground occupations of the free configurations 22000, 22100 and 22200
written with the lowest orbital as the least significant trit. -/
def reference (n : ℕ) : Basis n → Bool :=
  fun i => (codeOf i).val == (if n = 4 then 8 else if n = 5 then 17 else 26)

def contrastCenter : ℚ := 1 / 9000
def sectorRadius : ℚ := 1 / 100000
def predictedLo : ℚ := contrastCenter - 4 * sectorRadius
def predictedHi : ℚ := contrastCenter + 4 * sectorRadius

end Grain
