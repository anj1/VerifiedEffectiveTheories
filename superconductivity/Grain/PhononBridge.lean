import Grain.PhononExchange
import Grain.ShellValidation

/-! Transfer of the fixed-coupling mixed parity contrast through the
antiadiabatic electron–phonon energy comparison. The concrete Hamiltonian
and the proofs of the sector hypotheses are assembled in `Grain.PhononGround`. -/

namespace Grain.Phonon

open TwoShell Matrix
open scoped Matrix

noncomputable def frequency : ℝ := 5 * 10^13
noncomputable def mixing : ℝ := 1 / 10^8
noncomputable def phononTolerance : ℝ := 2 / 10^12

theorem frozen_coupling : 2 * frequency * mixing^2 = (coupling : ℝ) := by
  norm_num [frequency, mixing, coupling]

/-- The one-quantum compression keeps the energy dependence in its
discarded block. Each mode has electronic block `K + (ω - z) I`. -/
noncomputable def oneQuantumPivot {e m : Type} [DecidableEq e] [DecidableEq m]
    (K : Matrix e e ℝ) (ω z : ℝ) : Matrix (m × e) (m × e) ℝ :=
  fun i j => if i.1 = j.1 then (K + (ω - z) • 1) i.2 j.2 else 0

/-- Exact response of the vacuum/one-quantum compression at a nonsingular
shift. The two vertex factors surround the shifted electronic resolvent. -/
theorem one_quantum_response {e m : Type} [Fintype e] [Fintype m]
    [DecidableEq e] [DecidableEq m] (K : Matrix e e ℝ)
    (T : Matrix (m × e) e ℝ) (ω strength z : ℝ)
    (h : IsUnit (oneQuantumPivot (m := m) K ω z)) (x r : e → ℝ) :
    ((K - z • 1) - strength^2 • (Tᵀ * (oneQuantumPivot K ω z)⁻¹ * T)) *ᵥ x = r ↔
      ∃! y : m × e → ℝ,
        Matrix.fromBlocks (K - z • 1) (strength • Tᵀ) (strength • T) (oneQuantumPivot K ω z) *ᵥ
          Sum.elim x y = Sum.elim r 0 := by
  simpa only [schur, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_two] using
    schur_response (Matrix.fromBlocks (K - z • 1) (strength • Tᵀ) (strength • T)
      (oneQuantumPivot K ω z)) h x r

/-- With zero or one singly occupied sites, count the return hops on
pair–empty, pair–single, and single–empty bonds. The density contribution
is the sum of the squared site occupancies. -/
theorem frozen_diagonal_shift (n p e b : ℕ)
    (hn : n = 6 ∨ n = 7 ∨ n = 8) (hfilled : p + e + b = 7)
    (hnumber : 2*p + b = n) (hb : b ≤ 1) :
    (2*p*e + b*(p+e) + (n+2*p) : ℝ) = 24 + n + 2*p := by
  have he : 2*p*e + b*(p+e) = 24 := by
    rcases hn with rfl | rfl | rfl
    · have h : p = 3 ∧ e = 4 ∧ b = 0 := by omega
      rcases h with ⟨rfl, rfl, rfl⟩
      decide
    · have h : p = 3 ∧ e = 3 ∧ b = 1 := by omega
      rcases h with ⟨rfl, rfl, rfl⟩
      decide
    · have h : p = 4 ∧ e = 3 ∧ b = 0 := by omega
      rcases h with ⟨rfl, rfl, rfl⟩
      decide
  have hc : ((2*p*e + b*(p+e) : ℕ) : ℝ) = 24 := by exact_mod_cast he
  push_cast at hc
  linarith

noncomputable def electronicShift (k : Fin 3) : ℝ :=
  -(coupling : ℝ) * (12 + (6 + (k.val : ℝ)) / 2)

theorem shift_cancels : electronicShift 1 - (electronicShift 0 + electronicShift 2)/2 = 0 := by
  norm_num [electronicShift]
  ring

/-- Explicit variational error budget, uniform in the number of retained
higher phonon configurations. The hypotheses are electronic quadratic-form
bounds and the vacuum-to-one-quantum ladder rule. -/
theorem frozen_harmonic_bounds {e m p : Type} [Fintype e] [Fintype m] [Fintype p]
    (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (lower : m → (Option m ⊕ p → e → ℝ) → Option m ⊕ p → e → ℝ)
    (l u : ℝ) (hu0 : -81 ≤ u) (hu1 : u ≤ 80) (h0 : K 0 = 0)
    (hl : ∀ v, l * normSq v ≤ effective K A frequency mixing v)
    (x : e → ℝ) (hx : normSq x = 1) (hu : effective K A frequency mixing x ≤ u)
    (hK : ∀ y, K y ≤ 80 * normSq y)
    (hB : vertexNorm A x ≤ 112)
    (hL : ∀ j, lower j (lowState x (dressing A mixing x)) =
      lowAnnihilated (dressing A mixing x) j) :
    l ≤ sInf (normalizedEnergies (harmonicForm K A frequency mixing lower)) ∧
    sInf (normalizedEnergies (harmonicForm K A frequency mixing lower)) ≤
      u + phononTolerance := by
  apply harmonic_ground_bounds K A lower frequency mixing l u 80 112 phononTolerance
    (by norm_num [frequency]) h0 hl x hx hu hK hB (by linarith) (by norm_num [phononTolerance]) _ hL
  norm_num [mixing, phononTolerance]
  linarith

noncomputable def parity (E : Fin 3 → ℝ) : ℝ := E 1 - (E 0 + E 2) / 2

noncomputable def microscopicContrast (E : Bool → Bool → Fin 3 → ℝ) : ℝ :=
  parity (E false false) - parity (E false true) -
    parity (E true false) + parity (E true true)

private theorem parity_bounds (E : Bool → Bool → Fin 3 → ℝ)
    (h : ∀ r s k,
      Prediction.energy r s k + electronicShift k ≤ E r s k ∧
        E r s k ≤ Prediction.energy r s k + electronicShift k + phononTolerance)
    (r s : Bool) :
    Prediction.parityEnergy r s - phononTolerance ≤ parity (E r s) ∧
    parity (E r s) ≤ Prediction.parityEnergy r s + phononTolerance := by
  obtain ⟨l₀, u₀⟩ := h r s 0
  obtain ⟨l₁, u₁⟩ := h r s 1
  obtain ⟨l₂, u₂⟩ := h r s 2
  unfold parity Prediction.parityEnergy
  constructor <;> linarith [shift_cancels]

/-- The four-spectrum contrast remains positive after allowing the
proved harmonic-elimination error in each of the twelve energies.
`h` is the sector energy comparison for the chosen microscopic model. -/
theorem microscopic_contrast_positive (E : Bool → Bool → Fin 3 → ℝ)
    (h : ∀ r s k,
      Prediction.energy r s k + electronicShift k ≤ E r s k ∧
        E r s k ≤ Prediction.energy r s k + electronicShift k + phononTolerance) :
    0 < microscopicContrast E ∧
      |microscopicContrast E - Prediction.mixedContrast| ≤ 4 * phononTolerance := by
  obtain ⟨la, ua⟩ := parity_bounds E h false false
  obtain ⟨lb, ub⟩ := parity_bounds E h false true
  obtain ⟨lc, uc⟩ := parity_bounds E h true false
  obtain ⟨ld, ud⟩ := parity_bounds E h true true
  have hl : Prediction.mixedContrast - 4 * phononTolerance ≤ microscopicContrast E := by
    unfold Prediction.mixedContrast microscopicContrast
    linarith
  have hu : microscopicContrast E ≤ Prediction.mixedContrast + 4 * phononTolerance := by
    unfold Prediction.mixedContrast microscopicContrast
    linarith
  have hlow : (FullSolve.mixedLo : ℝ) ≤ Prediction.mixedContrast := FullSolve.mixed_bounds.1
  have hconst : (4 * phononTolerance : ℝ) < (FullSolve.mixedLo : ℝ) := by
    rw [FullSolve.full_endpoints.1]
    norm_num [phononTolerance]
  exact ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

end Grain.Phonon
