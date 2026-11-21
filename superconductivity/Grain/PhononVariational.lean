import Grain.Energy

/-! Variational control of elimination of harmonic modes. The electronic
vertices enter linearly. Eliminating the one-quantum amplitudes produces
the sum of squares of the vertices with a negative coefficient. -/

namespace Grain.Phonon

noncomputable section

variable {e m : Type} [Fintype e] [Fintype m]

def inner (x y : e → ℝ) : ℝ := ∑ i, x i * y i

theorem inner_self (x : e → ℝ) : inner x x = normSq x := by
  simp [inner, normSq, pow_two]

theorem normSq_nonneg (x : e → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem normSq_zero : normSq (0 : e → ℝ) = 0 := by simp [normSq]

theorem complete_square (x y : e → ℝ) (a : ℝ) :
    normSq (fun i => y i + a * x i) =
      normSq y + 2 * a * inner y x + a^2 * normSq x := by
  simp only [normSq, inner, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

def vertexNorm (A : m → (e → ℝ) → (e → ℝ)) (x : e → ℝ) : ℝ :=
  ∑ j, normSq (A j x)

def effective (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω a : ℝ) (x : e → ℝ) : ℝ := K x - ω * a^2 * vertexNorm A x

/-- Quadratic form of the harmonic Hamiltonian compressed to the vacuum
and all one-quantum states. Here `a` is the linear vertex divided by the
mode frequency. -/
def vacuumOneForm (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω a : ℝ) (x : e → ℝ) (y : m → e → ℝ) : ℝ :=
  K x + ∑ j, (K (y j) + ω * normSq (y j) + 2 * ω * a * inner (y j) (A j x))

def jointNormSq (x : e → ℝ) (y : m → e → ℝ) : ℝ :=
  normSq x + ∑ j, normSq (y j)

theorem vacuumOne_square (K : (e → ℝ) → ℝ)
    (A : m → (e → ℝ) → (e → ℝ)) (ω a : ℝ) (x : e → ℝ) (y : m → e → ℝ) :
    vacuumOneForm K A ω a x y =
      effective K A ω a x +
        ∑ j, (K (y j) + ω * normSq (fun i => y j i + a * A j x i)) := by
  simp only [vacuumOneForm, effective, vertexNorm, complete_square, mul_add,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The completing-square lower bound holds in every phonon space, when
`lowered` is the array of annihilated amplitudes. No bound on its size or
on the number of retained quanta is used. -/
theorem harmonic_lower {p : Type} [Fintype p]
    (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω a l : ℝ) (hω : 0 ≤ ω)
    (hl : ∀ v, l * normSq v ≤ effective K A ω a v)
    (ψ : p → e → ℝ) (lowered : m → p → e → ℝ) :
    l * (∑ q, normSq (ψ q)) ≤
      ∑ q, (K (ψ q) + ∑ j, (ω * normSq (lowered j q) +
        2 * ω * a * inner (lowered j q) (A j (ψ q)))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset m))
    (fun j _ => mul_nonneg hω (normSq_nonneg (fun i => lowered j q i + a * A j (ψ q) i)))
  simp only [complete_square, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have he := hl (ψ q)
  unfold effective vertexNorm at he
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith only [h, he]

def dressing (A : m → (e → ℝ) → (e → ℝ)) (a : ℝ) (x : e → ℝ) : m → e → ℝ :=
  fun j i => -a * A j x i

theorem dressing_norm (A : m → (e → ℝ) → (e → ℝ)) (a : ℝ) (x : e → ℝ) :
    jointNormSq x (dressing A a x) = normSq x + a^2 * vertexNorm A x := by
  simp [jointNormSq, dressing, normSq, mul_pow, vertexNorm, Finset.mul_sum]

theorem dressed_upper (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (ω a u κ B ε : ℝ) (x : e → ℝ)
    (hx : normSq x = 1) (hu : effective K A ω a x ≤ u)
    (hK : ∀ y, K y ≤ κ * normSq y)
    (hB : vertexNorm A x ≤ B) (hk : 0 ≤ κ - u) (hε : 0 ≤ ε)
    (hbudget : a^2 * B * (κ - u) ≤ ε) :
    0 < jointNormSq x (dressing A a x) ∧
    vacuumOneForm K A ω a x (dressing A a x) ≤
      (u + ε) * jointNormSq x (dressing A a x) := by
  have hn : 0 ≤ vertexNorm A x := Finset.sum_nonneg fun _ _ => normSq_nonneg _
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset m)) =>
    hK (dressing A a x j))
  rw [← Finset.mul_sum] at hsum
  have hnorm := dressing_norm A a x
  unfold jointNormSq at hnorm
  rw [add_right_inj] at hnorm
  rw [hnorm] at hsum
  have hsmall := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hB (sq_nonneg a)) hk
  have hlarge := mul_nonneg hε (mul_nonneg (sq_nonneg a) hn)
  rw [dressing_norm, hx, vacuumOne_square]
  have hzero (j : m) : (fun i => dressing A a x j i + a * A j x i) = 0 := by
    funext i
    simp [dressing]
  simp only [hzero, normSq_zero, mul_zero, add_zero]
  exact ⟨by positivity, by nlinarith only [hu, hsum, hnorm, hsmall, hbudget, hlarge]⟩

/-- The first sector is the vacuum, the other low sectors have one quantum.
The extra labels can include arbitrarily many higher harmonic occupations. -/
def lowState {p : Type} (x : e → ℝ) (y : m → e → ℝ) :
    Option m ⊕ p → e → ℝ :=
  Sum.elim (Option.elim' x y) (fun _ => 0)

def lowAnnihilated {p : Type} (y : m → e → ℝ) (j : m) :
    Option m ⊕ p → e → ℝ :=
  Sum.elim (Option.elim' (y j) (fun _ => 0)) (fun _ => 0)

def harmonicForm {p : Type} [Fintype p] (K : (e → ℝ) → ℝ)
    (A : m → (e → ℝ) → (e → ℝ)) (ω a : ℝ)
    (lower : m → (p → e → ℝ) → p → e → ℝ) (ψ : p → e → ℝ) : ℝ :=
  ∑ q, (K (ψ q) + ∑ j, (ω * normSq (lower j ψ q) +
    2 * ω * a * inner (lower j ψ q) (A j (ψ q))))

def normalizedEnergies {p : Type} [Fintype p] (Q : (p → e → ℝ) → ℝ) : Set ℝ :=
  { v | ∃ ψ, 0 < (∑ q, normSq (ψ q)) ∧ Q ψ / (∑ q, normSq (ψ q)) = v }

private theorem inner_zero_left (x : e → ℝ) : inner 0 x = 0 := by simp [inner]

/-- The upper trial uses only the vacuum and one-quantum amplitudes. Higher
phonon occupations can be included with any finite cutoff. The sole ladder
condition used for the upper bound is its action on those trial amplitudes. -/
theorem harmonic_ground_bounds {p : Type} [Fintype p]
    (K : (e → ℝ) → ℝ) (A : m → (e → ℝ) → (e → ℝ))
    (lower : m → (Option m ⊕ p → e → ℝ) → Option m ⊕ p → e → ℝ)
    (ω a l u κ B ε : ℝ)
    (hω : 0 ≤ ω) (h0 : K 0 = 0)
    (hl : ∀ v, l * normSq v ≤ effective K A ω a v)
    (x : e → ℝ) (hx : normSq x = 1) (hu : effective K A ω a x ≤ u)
    (hK : ∀ y, K y ≤ κ * normSq y)
    (hB : vertexNorm A x ≤ B) (hk : 0 ≤ κ - u) (hε : 0 ≤ ε)
    (hbudget : a^2 * B * (κ - u) ≤ ε)
    (hL : ∀ j, lower j (lowState x (dressing A a x)) = lowAnnihilated (dressing A a x) j) :
    l ≤ sInf (normalizedEnergies (harmonicForm K A ω a lower)) ∧
      sInf (normalizedEnergies (harmonicForm K A ω a lower)) ≤ u + ε := by
  let y := dressing A a x
  let ψ : Option m ⊕ p → e → ℝ := lowState x y
  have hlb : ∀ E ∈ normalizedEnergies (harmonicForm K A ω a lower), l ≤ E := by
    rintro E ⟨v, hpos, rfl⟩
    exact (le_div_iff₀ hpos).2 (harmonic_lower K A ω a l hω hl v (fun j => lower j v))
  obtain ⟨hpos, hup⟩ := dressed_upper K A ω a u κ B ε x hx hu hK hB hk hε hbudget
  have hnorm : (∑ q, normSq (ψ q)) = jointNormSq x y := by
    simp [ψ, lowState, jointNormSq, Fintype.sum_sum_type, Fintype.sum_option, normSq_zero]
  have hL' (j : m) : lower j ψ = lowAnnihilated y j := hL j
  have hform : harmonicForm K A ω a lower ψ = vacuumOneForm K A ω a x y := by
    simp only [harmonicForm, hL']
    simp only [ψ, Fintype.sum_sum_type, Fintype.sum_option,
      lowState, lowAnnihilated, Sum.elim_inl, Sum.elim_inr, Option.elim'_none, Option.elim'_some,
      normSq_zero, inner_zero_left, mul_zero, add_zero, Finset.sum_const_zero, h0, vacuumOneForm]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have epos : 0 < ∑ q, normSq (ψ q) := hnorm.symm ▸ hpos
  let E := harmonicForm K A ω a lower ψ / (∑ q, normSq (ψ q))
  have he : E ∈ normalizedEnergies (harmonicForm K A ω a lower) := ⟨ψ, epos, rfl⟩
  have heu : E ≤ u + ε := by
    apply (div_le_iff₀ epos).2
    rw [hform, hnorm]
    exact hup
  exact ⟨le_csInf ⟨E, he⟩ hlb, (csInf_le ⟨l, hlb⟩ he).trans heu⟩

end

end Grain.Phonon
