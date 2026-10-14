import Mathlib

/-!
Exact algebra for a *specified* linear probe coupling. This does not derive
Maxwell scattering, the coupling coefficient, or the weak-scattering regime.
-/
namespace LatticeGas.Scattering

open Complex

theorem amplitude_linear {α : Type*} [Fintype α] (a : ℂ)
    (density phase : α → ℂ) :
    (∑ x, (a * density x) * phase x) =
      a * (∑ x, density x * phase x) := by
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

theorem intensity_structure_factor {α : Type*} [Fintype α] (a : ℂ)
    (density phase : α → ℂ) :
    Complex.normSq (∑ x, (a * density x) * phase x) =
      Complex.normSq a * Complex.normSq (∑ x, density x * phase x) := by
  rw [amplitude_linear]
  exact Complex.normSq_mul a _

end LatticeGas.Scattering
