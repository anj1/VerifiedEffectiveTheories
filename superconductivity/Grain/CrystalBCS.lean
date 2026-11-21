import Grain.BCS

/-! Static reduction of a finite real, spin-degenerate site Hamiltonian
with independent harmonic site coordinates. A site couples to its total
electron density. The retained Cooper channels are pairs of time-reversed
normal states. The crystal data are effective-model inputs. -/

namespace Grain.CrystalBCS

structure Crystal (s : Type) where
  bare : s → s → ℚ
  stiffness : s → ℚ
  deformation : s → ℚ
  repulsion : s → ℚ
  chemicalPotential : ℚ

def induced (c : Crystal s) (a : s) : ℚ := c.deformation a ^ 2 / c.stiffness a

def attraction (c : Crystal s) (a : s) : ℚ := induced c a - c.repulsion a

def normal [DecidableEq s] (c : Crystal s) (a b : s) : ℚ :=
  c.bare a b - if a = b then induced c a / 2 else 0

noncomputable def localEnergy (stiffness deformation repulsion : ℝ) (up down : Bool) (q : ℝ) : ℝ :=
  stiffness * q^2 / 2 + deformation * q * (up.toNat + down.toNat) +
    repulsion * up.toNat * down.toNat

theorem relaxed_site (stiffness deformation repulsion : ℝ) (hk : stiffness ≠ 0)
    (up down : Bool) (q : ℝ) :
    localEnergy stiffness deformation repulsion up down q =
      stiffness / 2 * (q + deformation * (up.toNat + down.toNat) / stiffness)^2 -
        deformation^2 / stiffness / 2 * (up.toNat + down.toNat) +
        (repulsion - deformation^2 / stiffness) * up.toNat * down.toNat := by
  cases up <;> cases down <;> simp [localEnergy] <;> field_simp <;> ring

theorem static_minimum (stiffness deformation repulsion : ℝ) (hk : 0 < stiffness)
    (up down : Bool) :
    let q := -(deformation * (up.toNat + down.toNat)) / stiffness
    (∀ z, localEnergy stiffness deformation repulsion up down q ≤
      localEnergy stiffness deformation repulsion up down z) := by
  intro q z
  rw [relaxed_site _ _ _ hk.ne', relaxed_site _ _ _ hk.ne']
  have hq : q + deformation * (up.toNat + down.toNat) / stiffness = 0 := by
    simp [q, neg_div]
  rw [hq]
  have hs : 0 ≤ stiffness / 2 * (z + deformation *
      (up.toNat + down.toNat) / stiffness)^2 := by positivity
  nlinarith

/-- At the relaxed coordinate the one-body shift and the on-site pair
interaction are exactly the coefficients used by the normal and Cooper
matrices below. -/
theorem static_coefficients (c : Crystal s) (a : s) (hk : c.stiffness a ≠ 0)
    (up down : Bool) :
    let q := -((c.deformation a : ℝ) * (up.toNat + down.toNat)) / (c.stiffness a : ℝ)
    localEnergy (c.stiffness a) (c.deformation a) (c.repulsion a) up down q =
      -(induced c a : ℝ) / 2 * (up.toNat + down.toNat) -
        (attraction c a : ℝ) * up.toNat * down.toNat := by
  intro q
  rw [relaxed_site _ _ _ (by exact_mod_cast hk)]
  have hq : q + (c.deformation a : ℝ) * (up.toNat + down.toNat) / (c.stiffness a : ℝ) = 0 := by
    simp [q, neg_div]
  rw [hq]
  unfold attraction induced
  push_cast
  ring

structure BandData (s : Type) where
  level : s → ℚ
  orbital : s → s → ℚ

section Bands

variable {s : Type} [Fintype s] [DecidableEq s]

def orbitalNorm (b : BandData s) (i : s) : ℚ := ∑ a, b.orbital a i ^ 2

def xi (c : Crystal s) (b : BandData s) (i : s) : ℚ := b.level i - c.chemicalPotential

def normalTest (c : Crystal s) (b : BandData s) : Prop :=
  (∀ i, 0 < orbitalNorm b i) ∧
  (∀ i j, (∑ a, b.orbital a i * b.orbital a j) =
    if i = j then orbitalNorm b i else 0) ∧
  (∀ a d, (∑ i, b.orbital a i * b.orbital d i / orbitalNorm b i) =
    if a = d then 1 else 0) ∧
  (∀ a i, action (normal c) (fun d => b.orbital d i) a = b.level i * b.orbital a i)

instance (c : Crystal s) (b : BandData s) : Decidable (normalTest c b) := by
  unfold normalTest
  infer_instance

/-- The verified projectors resolve the identity on the whole site basis. -/
theorem complete_band_basis (c : Crystal s) (b : BandData s) (h : normalTest c b)
    (v : s → ℚ) (a : s) :
    (∑ i, (∑ d, b.orbital a i * b.orbital d i / orbitalNorm b i * v d)) = v a := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, h.2.2.1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

def cooperKernel (c : Crystal s) (b : BandData s) (i j : s) : ℚ :=
  ∑ a, attraction c a * b.orbital a i ^ 2 * b.orbital a j ^ 2 /
    (orbitalNorm b i * orbitalNorm b j)

/-- Projection of the local two-body attraction on the normal-state pair
wavefunctions. The interaction acts only at coincident site indices.
The normalization is the norm of each product of two orbital vectors. -/
theorem projected_cooper (c : Crystal s) (b : BandData s) (i j : s) :
    (∑ ab : s × s, if ab.1 = ab.2 then
      attraction c ab.1 * (b.orbital ab.1 i * b.orbital ab.2 i) *
        (b.orbital ab.1 j * b.orbital ab.2 j) / (orbitalNorm b i * orbitalNorm b j)
      else 0) = cooperKernel c b i j := by
  rw [Fintype.sum_prod_type]
  unfold cooperKernel
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp [pow_two]
  · exact fun d _ hd => ite_eq_right (Ne.symm hd)
  · simp

def constantChannel (c : Crystal s) (b : BandData s) (g : ℚ) : Prop :=
  ∀ i j, cooperKernel c b i j = g

instance (c : Crystal s) (b : BandData s) (g : ℚ) : Decidable (constantChannel c b g) := by
  unfold constantChannel
  infer_instance

omit [DecidableEq s] in
/-- A nonzero solution of the projected gap equation is constant across the
band indices when the computed Cooper matrix is constant. -/
theorem constant_solution [Nonempty s] (c : Crystal s) (b : BandData s)
    (g : ℚ) (h : constantChannel c b g) (chi : s → ℝ) (gap : s → ℝ)
    (he : ∀ i, gap i = ∑ j, (cooperKernel c b i j : ℝ) * (gap j * chi j))
    (hn : gap ≠ 0) :
    ∃ delta : ℝ, delta ≠ 0 ∧ (∀ i, gap i = delta) ∧ (g : ℝ) * (∑ j, chi j) = 1 := by
  let delta := (g : ℝ) * ∑ j, gap j * chi j
  have hk (i j : s) : cooperKernel c b i j = g := h i j
  have hd (i : s) : gap i = delta := by
    simpa only [hk, ← Finset.mul_sum, delta] using he i
  have hne : delta ≠ 0 := fun hz => hn (funext fun i => (hd i).trans hz)
  refine ⟨delta, hne, hd, (BCS.nonzero_constant_gap_iff chi g delta hne).1 ?_⟩
  calc
    delta = (g : ℝ) * (∑ j, gap j * chi j) := rfl
    _ = (g : ℝ) * (∑ j, delta * chi j) := by
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hd j]

end Bands

section Gap

variable {s : Type} [Fintype s]

noncomputable def normalPairResponse (c : Crystal s) (b : BandData s)
    (t : ℝ) (v : s → ℝ) (i : s) : ℝ :=
  ∑ j, (cooperKernel c b i j : ℝ) *
    (BCS.thermalFactor (|(xi c b j : ℝ)| / t) / (2 * |(xi c b j : ℝ)|) * v j)

def realGrowths (c : Crystal s) (b : BandData s) (t : ℝ) : Set ℝ :=
  {growth : ℝ | ∃ v : s → ℝ, v ≠ 0 ∧ ∀ i, normalPairResponse c b t v i = growth * v i}

/-- The scalar normal response is the top real growth eigenvalue of the
linearized finite-band gap equation on a constant attractive channel. -/
theorem leading_normal_growth [Nonempty s] (c : Crystal s) (b : BandData s) (g : ℚ)
    (hc : constantChannel c b g) (hg : 0 ≤ g) {t : ℝ} (ht : 0 < t) :
    IsGreatest (realGrowths c b t) (BCS.criticalResponse (xi c b) g t) := by
  let chi (j : s) := BCS.thermalFactor (|(xi c b j : ℝ)| / t) / (2 * |(xi c b j : ℝ)|)
  have hχ (j : s) : 0 ≤ chi j := by
    unfold chi BCS.thermalFactor
    apply div_nonneg _ (by positivity)
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by positivity))) (by positivity)
  have hcast : (0 : ℝ) ≤ g := by exact_mod_cast hg
  have hk (i j : s) : cooperKernel c b i j = g := hc i j
  constructor
  · refine ⟨fun _ => 1, ?_, fun i => ?_⟩
    · intro he
      have e := congrFun he (Classical.arbitrary s)
      norm_num at e
    · simp only [normalPairResponse, hk, mul_one, ← Finset.mul_sum, BCS.criticalResponse]
  · rintro growth ⟨v, hv, he⟩
    have he' (i : s) : (g : ℝ) * (∑ j, chi j * v j) = growth * v i := by
      simpa only [normalPairResponse, hk, ← Finset.mul_sum, chi] using he i
    rcases BCS.rank_one_growth chi g growth v hv he' with h | h
    · rw [h]
      exact mul_nonneg hcast (Finset.sum_nonneg fun i _ => hχ i)
    · exact h.le

noncomputable def zeroGapEquation (c : Crystal s) (b : BandData s) (gap : s → ℝ) : Prop :=
  ∀ i, gap i = ∑ j, (cooperKernel c b i j : ℝ) *
    (gap j * (1 / (2 * BCS.quasiparticle (xi c b j : ℝ) (gap j))))

theorem zero_gap_equation [Nonempty s] (c : Crystal s) (b : BandData s)
    (g : ℚ) (hc : constantChannel c b g) {delta : ℝ} (hd : delta ≠ 0) :
    zeroGapEquation c b (fun _ => delta) ↔ BCS.zeroResponse (xi c b) g delta = 1 := by
  have hk (i j : s) : cooperKernel c b i j = g := hc i j
  let chi (j : s) := 1 / (2 * BCS.quasiparticle (xi c b j : ℝ) delta)
  have hsum (i : s) : (∑ j, (cooperKernel c b i j : ℝ) * (delta * chi j)) =
      (g : ℝ) * ∑ j, delta * chi j := by simp only [hk, Finset.mul_sum]
  change (∀ i, delta = ∑ j, (cooperKernel c b i j : ℝ) * (delta * chi j)) ↔ _
  simp only [hsum, BCS.nonzero_constant_gap_iff _ _ _ hd, BCS.zeroResponse, chi]
  exact ⟨fun h => h (Classical.arbitrary s), fun h _ => h⟩

end Gap

/-- A real periodic lattice with two sites along each of its periodic
directions. A power-of-two basis size is checked by the generator and
the electronic reconstruction is checked independently in Lean. -/
def periodicCrystal {N : ℕ} [NeZero N] (hopping : Fin N → ℚ)
    (stiffness deformation repulsion chemicalPotential : ℚ) : Crystal (Fin N) where
  bare a b := hopping (Fin.ofNat N (a.val ^^^ b.val))
  stiffness _ := stiffness
  deformation _ := deformation
  repulsion _ := repulsion
  chemicalPotential := chemicalPotential

def character (a i : Fin N) : ℚ :=
  (-1 : ℚ) ^ (∑ k ∈ Finset.range (Nat.log2 N), ((a.val &&& i.val).testBit k).toNat)

/-- The coefficient at the origin is one, so evaluating the normal
Hamiltonian there gives the proposed energy of each periodic orbital. -/
def periodicBands {N : ℕ} [NeZero N] (c : Crystal (Fin N)) : BandData (Fin N) where
  orbital := character
  level i := action (normal c) (fun a => character a i) 0

end Grain.CrystalBCS
