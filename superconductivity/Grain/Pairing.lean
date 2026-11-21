import Grain.Energy

/-! The finite, even-frequency linearized gap equation on weighted Fermi-surface
patches. Energies are in meV and the temperature variable is `π k_B T`.
The mode energies, squared vertices and screened Coulomb matrix are inputs. -/

namespace Grain.Pairing

structure Mode where
  energy : ℚ
  vertexSq : ℚ

structure Input (p : Type) where
  weight : p → ℚ
  modes : p → p → List Mode
  coulomb : p → p → ℚ

def phonon (data : Input p) (i j : p) (transfer : ℚ) : ℚ :=
  ((data.modes i j).map fun m =>
    2 * m.energy * m.vertexSq / (m.energy ^ 2 + transfer ^ 2)).sum

def frequencyIndex (n : Fin N) : ℚ := 2 * (n.val : ℚ) + 1

def pairWeight (data : Input p) (a : p × Fin N) : ℚ :=
  data.weight a.1 / frequencyIndex a.2

def transfers (t : ℚ) (n m : Fin N) : ℚ × ℚ :=
  (t * (frequencyIndex n - frequencyIndex m), t * (frequencyIndex n + frequencyIndex m))

def kernel (data : Input p) (t : ℚ) (a b : p × Fin N) : ℚ :=
  let v := transfers t a.2 b.2
  phonon data a.1 b.1 v.1 + phonon data a.1 b.1 v.2 - 2 * data.coulomb a.1 b.1

def renormalization [Fintype p] (data : Input p) (t : ℚ) (a : p × Fin N) : ℚ :=
  1 + (∑ b : p × Fin N,
    let v := transfers t a.2 b.2
    data.weight b.1 * (phonon data a.1 b.1 v.1 - phonon data a.1 b.1 v.2)) /
      frequencyIndex a.2

def metric [Fintype p] (data : Input p) (t : ℚ) (a : p × Fin N) : ℚ :=
  renormalization data t a / pairWeight data a

theorem kernel_symm (data : Input p) (t : ℚ)
    (hm : ∀ i j, data.modes i j = data.modes j i)
    (hc : ∀ i j, data.coulomb i j = data.coulomb j i)
    (a b : p × Fin N) : kernel data t a b = kernel data t b a := by
  have hd : t * (frequencyIndex b.2 - frequencyIndex a.2) =
      -(t * (frequencyIndex a.2 - frequencyIndex b.2)) := by ring
  simp [kernel, transfers, phonon, hd, hm b.1 a.1, hc b.1 a.1,
    add_comm (frequencyIndex b.2) (frequencyIndex a.2)]

/-- Multiplying the gap amplitudes by their positive pair weights turns the
gap equation into a symmetric generalized eigenproblem. -/
theorem gap_equation [Fintype p] (data : Input p) (t : ℚ) (growth : ℝ)
    (gap : p × Fin N → ℝ) (hw : ∀ a : p × Fin N, pairWeight data a ≠ 0) :
    let x := fun a => (pairWeight data a : ℝ) * gap a
    let response := fun a => ∑ b, (kernel data t a b : ℝ) * x b
    (∀ a, response a = growth * (renormalization data t a : ℝ) * gap a) ↔
    (∀ a, response a = growth * (metric data t a : ℝ) * x a) := by
  dsimp
  unfold metric
  have cancel (a : p × Fin N) :
      growth * ((renormalization data t a / pairWeight data a : ℚ) : ℝ) *
          ((pairWeight data a : ℝ) * gap a) =
        growth * (renormalization data t a : ℝ) * gap a := by
    have hn : (pairWeight data a : ℝ) ≠ 0 := by exact_mod_cast hw a
    push_cast
    field_simp
  simp only [cancel]

section Bounds

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def metricForm (d : ι → ℚ) (x : ι → ℝ) : ℝ :=
  ∑ i, (d i : ℝ) * x i ^ 2

def rationalMetricForm (d x : ι → ℚ) : ℚ := ∑ i, d i * x i ^ 2

noncomputable def quotients (A : ι → ι → ℚ) (d : ι → ℚ) : Set ℝ :=
  {q | ∃ x, 0 < metricForm d x ∧ q = form A x / metricForm d x}

/-- The top Rayleigh value of the pencil, equal to its largest eigenvalue
when the kernel is symmetric and the diagonal metric is positive. -/
noncomputable def leading (A : ι → ι → ℚ) (d : ι → ℚ) : ℝ :=
  sSup (quotients A d)

def upperTest (A : ι → ι → ℚ) (d : ι → ℚ) (hi : ℚ)
    (L : ι → ι → ℚ) (pivot : ι → ℚ) : Prop :=
  (∀ k, 0 ≤ pivot k) ∧
    ∀ i j, (if i = j then hi * d i else 0) - A i j = ∑ k, L i k * pivot k * L j k

def lowerTest (A : ι → ι → ℚ) (d : ι → ℚ) (lo : ℚ) (x : ι → ℚ) : Prop :=
  0 < rationalMetricForm d x ∧ lo * rationalMetricForm d x ≤ rayleighNumerator A x

instance (A : ι → ι → ℚ) (d : ι → ℚ) (hi : ℚ) (L : ι → ι → ℚ) (pivot : ι → ℚ) :
    Decidable (upperTest A d hi L pivot) := by unfold upperTest; infer_instance

instance (A : ι → ι → ℚ) (d : ι → ℚ) (lo : ℚ) (x : ι → ℚ) :
    Decidable (lowerTest A d lo x) := by unfold lowerTest; infer_instance

omit [DecidableEq ι] in
private theorem gram_form (L : ι → ι → ℚ) (pivot : ι → ℚ) (x : ι → ℝ) :
    form (fun i j => ∑ k, L i k * pivot k * L j k) x =
      ∑ k, (pivot k : ℝ) * (∑ i, (L i k : ℝ) * x i) ^ 2 := by
  unfold form
  simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pencil_upper (A : ι → ι → ℚ) (d : ι → ℚ) (hi : ℚ)
    (L : ι → ι → ℚ) (pivot : ι → ℚ) (h : upperTest A d hi L pivot)
    (x : ι → ℝ) : form A x ≤ (hi : ℝ) * metricForm d x := by
  let M : ι → ι → ℚ := fun i j => if i = j then hi * d i else 0
  have he : (fun i j => M i j - A i j) = fun i j => ∑ k, L i k * pivot k * L j k :=
    funext fun i => funext (h.2 i)
  have hp : 0 ≤ form (fun i j => M i j - A i j) x := by
    rw [he, gram_form]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by exact_mod_cast h.1 k) (sq_nonneg _)
  rw [form_sub] at hp
  have hm : form M x = (hi : ℝ) * metricForm d x := by
    simp [form, M, metricForm, apply_ite (fun q : ℚ => (q : ℝ)), ite_mul, Finset.mul_sum, mul_assoc,
      pow_two]
  linarith

theorem eigenvalue_bounds (A : ι → ι → ℚ) (d : ι → ℚ) (lo hi : ℚ)
    (x : ι → ℚ) (L : ι → ι → ℚ) (pivot : ι → ℚ)
    (hl : lowerTest A d lo x) (hu : upperTest A d hi L pivot) :
    (lo : ℝ) ≤ leading A d ∧ leading A d ≤ (hi : ℝ) := by
  let y : ι → ℝ := fun i => (x i : ℝ)
  have hm : metricForm d y = (rationalMetricForm d x : ℝ) := by
    simp [metricForm, rationalMetricForm, y]
  have hn : 0 < metricForm d y := by rw [hm]; exact_mod_cast hl.1
  have hx : form A y / metricForm d y ∈ quotients A d := ⟨y, hn, rfl⟩
  have hbound : ∀ q ∈ quotients A d, q ≤ (hi : ℝ) := by
    rintro _ ⟨v, hv, rfl⟩
    exact (div_le_iff₀ hv).2 (pencil_upper A d hi L pivot hu v)
  have htrial : (lo : ℝ) ≤ form A y / metricForm d y := by
    apply (le_div_iff₀ hn).2
    rw [hm, form_cast]
    exact_mod_cast hl.2
  exact ⟨htrial.trans (le_csSup ⟨hi, hbound⟩ hx), csSup_le ⟨_, hx⟩ hbound⟩

end Bounds

end Grain.Pairing
