import Grain.ParityCancellation
import Grain.TwoShell

/-! Match the parity energy after removing symmetric shells. -/

namespace Grain.ParityMatching

open ParityCancellation

/-- The coefficient of `g²` in the parity contribution of the removed shells. -/
def parityCoefficient {ι : Type} [Fintype ι] (radius : ι → ℚ) : ℚ :=
  ∑ i, 1 / (2 * radius i)

theorem symmetric_hop_parity {ι : Type} [Fintype ι] (g : ℚ) (radius : ι → ℚ) :
    (virtualHopSum g (-radius) radius 0 + virtualHopSum g (-radius) radius 2) / 2 -
        virtualHopSum g (-radius) radius 1 = g ^ 2 * parityCoefficient radius := by
  rw [secondOrder_parity]
  simp only [Pi.neg_apply, neg_neg, parityCoefficient, div_eq_mul_inv, mul_inv_rev, one_mul,
    ← Finset.sum_mul]
  ring

/-- Parity of a frozen background and the three central occupations at coupling `g`. -/
def bareCentralParity (g background offset : ℚ) : ℚ :=
  (background + offset) - (background + (background + 2 * offset - g)) / 2

theorem bareCentralParity_eq (g background offset : ℚ) :
    bareCentralParity g background offset = g / 2 := by
  unfold bareCentralParity
  ring

def matchedShift {ι : Type} [Fintype ι] (g : ℚ) (radius : ι → ℚ) : ℚ :=
  g ^ 2 * (2 * parityCoefficient radius)

/-- Matching bare central parity to the second-order shell contribution fixes the shift. -/
theorem matches_parity_iff {ι : Type} [Fintype ι] (g background offset δ : ℚ) (radius : ι → ℚ) :
    bareCentralParity (g + δ) background offset =
        bareCentralParity g background offset + g ^ 2 * parityCoefficient radius ↔
      δ = matchedShift g radius := by
  rw [bareCentralParity_eq, bareCentralParity_eq, matchedShift]
  constructor <;> intro h <;> linarith

theorem two_shell_shift (g r s : ℚ) :
    matchedShift g ![r, s] = g ^ 2 * (1 / r + 1 / s) := by
  simp only [matchedShift, parityCoefficient, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The reciprocal completion of the second-order matching rule. -/
def reciprocalCoupling (g inverseShift : ℚ) : ℚ :=
  g / (1 - g * inverseShift)

theorem reciprocalCoupling_eq {g : ℚ} (hg : g ≠ 0) (inverseShift : ℚ) :
    reciprocalCoupling g inverseShift = 1 / (1 / g - inverseShift) := by
  rw [reciprocalCoupling, show 1 - g * inverseShift = g * (1 / g - inverseShift) by
    rw [mul_sub, mul_one_div_cancel hg]]
  rw [div_mul_eq_div_div, div_self hg]

/-- After matching through order `g²`, the reciprocal control chooses this cubic remainder. -/
theorem reciprocal_remainder {g inverseShift : ℚ} (h : 1 - g * inverseShift ≠ 0) :
    reciprocalCoupling g inverseShift - (g + g ^ 2 * inverseShift) =
      g ^ 3 * inverseShift ^ 2 / (1 - g * inverseShift) := by
  unfold reciprocalCoupling
  field_simp
  ring

/-- A mixed contrast annihilates every sum of a common term and independent shell terms. -/
theorem mixed_additive_zero {R S : Type} (base : ℚ) (f : R → ℚ) (h : S → ℚ)
    (r₁ r₂ : R) (s₁ s₂ : S) :
    (base + f r₁ + h s₁) - (base + f r₁ + h s₂) -
      (base + f r₂ + h s₁) + (base + f r₂ + h s₂) = 0 := by
  ring

/-- The bare parity plus the virtual-hop contribution for the seven-orbital spectrum. -/
def benchmarkParitySecondOrder (g d r s : ℚ) : ℚ :=
  let radius : Fin 3 → ℚ := ![d, r, s]
  g / 2 + ((virtualHopSum g (-radius) radius 0 + virtualHopSum g (-radius) radius 2) / 2 -
    virtualHopSum g (-radius) radius 1)

theorem benchmark_mixed_zero (g d r₁ r₂ s₁ s₂ : ℚ) :
    benchmarkParitySecondOrder g d r₁ s₁ - benchmarkParitySecondOrder g d r₁ s₂ -
      benchmarkParitySecondOrder g d r₂ s₁ + benchmarkParitySecondOrder g d r₂ s₂ = 0 := by
  have expand (r s : ℚ) : benchmarkParitySecondOrder g d r s =
      (g / 2 + g ^ 2 / (2 * d)) + g ^ 2 / (2 * r) + g ^ 2 / (2 * s) := by
    simp only [benchmarkParitySecondOrder, symmetric_hop_parity]
    simp [parityCoefficient, Fin.sum_univ_succ]
    ring
  simp only [expand]
  exact mixed_additive_zero _ (fun r => g ^ 2 / (2 * r)) (fun s => g ^ 2 / (2 * s)) _ _ _ _

private def centralWeight (r : ℚ) : ℚ := 1 / (2 * r)
private def pairWeight (r s : ℚ) : ℚ := 1 / (2 * (r + s))

/-- The ordered three-hop loops involving the central orbital. The first sum
joins two distinct central hops. The second joins a central hop and an ordinary
hop sharing its other endpoint, counting both orientations. -/
def centralLoopSum {ι : Type} [Fintype ι] [DecidableEq ι] (radius : ι → ℚ) : ℚ :=
  (∑ i, ∑ j, if i = j then 0 else centralWeight (radius i) * centralWeight (radius j)) +
    2 * ∑ i, ∑ j, centralWeight (radius i) * pairWeight (radius i) (radius j)

/-- The resulting cubic coefficient of the parity energy. -/
def cubicParityCoefficient {ι : Type} [Fintype ι] (radius : ι → ℚ) : ℚ :=
  2 * parityCoefficient radius ^ 2 - ∑ i, centralWeight (radius i) ^ 2

theorem central_loop_sum_eq {ι : Type} [Fintype ι] [DecidableEq ι] (radius : ι → ℚ)
    (hr : ∀ i, 0 < radius i) : centralLoopSum radius = cubicParityCoefficient radius := by
  let w := centralWeight ∘ radius
  let p := fun i j => pairWeight (radius i) (radius j)
  have hpair (i j : ι) : p j i = p i j := by simp [p, pairWeight, add_comm]
  have hweight (i j : ι) : (w i + w j) * p i j = w i * w j := by
    dsimp [w, p, centralWeight, pairWeight]
    field_simp [(hr i).ne', (hr j).ne', (add_pos (hr i) (hr j)).ne']
    ring
  have hdiag (i j : ι) : (if i = j then 0 else w i * w j) =
      w i * w j - (if i = j then w i ^ 2 else 0) := by
    by_cases h : i = j <;> simp [h, pow_two]
  have hprod : (∑ i, ∑ j, w i * w j) = (∑ i, w i) ^ 2 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hoff : (∑ i, ∑ j, if i = j then 0 else w i * w j) =
      (∑ i, w i) ^ 2 - ∑ i, w i ^ 2 := by
    simp_rw [hdiag, Finset.sum_sub_distrib]
    rw [hprod]
    simp
  have hswap : (∑ i, ∑ j, w j * p i j) = ∑ i, ∑ j, w i * p i j := by
    rw [Finset.sum_comm]
    simp_rw [hpair]
  have hcross : 2 * (∑ i, ∑ j, w i * p i j) = (∑ i, w i) ^ 2 := by
    calc
      2 * (∑ i, ∑ j, w i * p i j) =
          (∑ i, ∑ j, w i * p i j) + (∑ i, ∑ j, w j * p i j) := by rw [hswap, two_mul]
      _ = (∑ i, ∑ j, w i * w j) := by
        simp_rw [← Finset.sum_add_distrib, ← add_mul, hweight]
      _ = _ := hprod
  change (∑ i, ∑ j, if i = j then 0 else w i * w j) +
    2 * (∑ i, ∑ j, w i * p i j) = 2 * (∑ i, w i) ^ 2 - ∑ i, w i ^ 2
  rw [hoff, hcross]
  ring

private def reference (c : Fin 3) : TwoShell.Occupation := ![2, 2, 2, c, 0, 0, 0]
private def lowerOrbital (i : Fin 3) : Fin 7 := ![2, 1, 0] i
private def upperOrbital (i : Fin 3) : Fin 7 := ![4, 5, 6] i

private def ordinaryHop (c i j : Fin 3) : TwoShell.Occupation :=
  TwoShell.move (reference c) (lowerOrbital i) (upperOrbital j)

private def centerHop (c i : Fin 3) : TwoShell.Occupation :=
  if c = 0 then TwoShell.move (reference c) (lowerOrbital i) 3
  else TwoShell.move (reference c) 3 (upperOrbital i)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The first and last hops of every loop must use one of these endpoints. -/
theorem benchmark_legal_endpoints (c : Fin 3) (source target : Fin 7) :
    (reference c source = 2 ∧ reference c target = 0) ↔
      (∃ i j, source = lowerOrbital i ∧ target = upperOrbital j) ∨
      (c = 0 ∧ target = 3 ∧ ∃ i, source = lowerOrbital i) ∨
      (c = 2 ∧ source = 3 ∧ ∃ j, target = upperOrbital j) := by
  revert c source target
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem ordinary_edge (c i j k l : Fin 3) :
    TwoShell.Hop (ordinaryHop c i j) (ordinaryHop c k l) ↔
      (i = k ∧ j ≠ l) ∨ (j = l ∧ i ≠ k) := by
  revert c i j k l
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem center_edge (c i j : Fin 3) (hc : c ≠ 1) :
    TwoShell.Hop (centerHop c i) (centerHop c j) ↔ i ≠ j := by
  revert c i j
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem center_ordinary_edge (c i j k : Fin 3) (hc : c ≠ 1) :
    TwoShell.Hop (centerHop c i) (ordinaryHop c j k) ↔
      if c = 0 then j = i else k = i := by
  revert c i j k
  decide +kernel

/-- Ordered loop coefficient after reindexing the reference neighbors by their endpoints.
The mixed routes are doubled by `TwoShell.Hop.reverse`. -/
def benchmarkLoopSum (c : Fin 3) (radius : Fin 3 → ℚ) : ℚ :=
  (∑ i, ∑ j, ∑ k, ∑ l,
    if TwoShell.Hop (ordinaryHop c i j) (ordinaryHop c k l) then
      pairWeight (radius i) (radius j) * pairWeight (radius k) (radius l) else 0) +
  if c = 1 then 0 else
    (∑ i, ∑ j, if TwoShell.Hop (centerHop c i) (centerHop c j) then
      centralWeight (radius i) * centralWeight (radius j) else 0) +
    2 * ∑ i, ∑ j, ∑ k, if TwoShell.Hop (centerHop c i) (ordinaryHop c j k) then
      centralWeight (radius i) * pairWeight (radius j) (radius k) else 0

theorem benchmark_loop_parity (radius : Fin 3 → ℚ) (hr : ∀ i, 0 < radius i) :
    (benchmarkLoopSum 0 radius + benchmarkLoopSum 2 radius) / 2 -
      benchmarkLoopSum 1 radius = cubicParityCoefficient radius := by
  have noHop (i j : Fin 3) :
      (if i ≠ j then centralWeight (radius i) * centralWeight (radius j) else 0) =
        if i = j then 0 else centralWeight (radius i) * centralWeight (radius j) := by
    by_cases h : i = j <;> simp [h]
  have cross (i : Fin 3) :
      (∑ j, ∑ k, if k = i then centralWeight (radius i) * pairWeight (radius j) (radius k)
        else 0) = ∑ j, centralWeight (radius i) * pairWeight (radius i) (radius j) := by
    simp [pairWeight, add_comm]
  have crossEmpty (i : Fin 3) :
      (∑ j, ∑ k, if j = i then centralWeight (radius i) * pairWeight (radius j) (radius k)
        else 0) = ∑ j, centralWeight (radius i) * pairWeight (radius i) (radius j) := by
    rw [Finset.sum_comm]
    simp
  rw [← central_loop_sum_eq radius hr]
  simp only [benchmarkLoopSum, ordinary_edge, center_edge 0 _ _ (by decide),
    center_edge 2 _ _ (by decide), center_ordinary_edge 0 _ _ _ (by decide),
    center_ordinary_edge 2 _ _ _ (by decide), Fin.reduceEq, ite_true, ite_false, noHop,
    cross, crossEmpty, centralLoopSum, add_zero]
  ring

private theorem cubic_coefficient_three (d r s : ℚ) :
    cubicParityCoefficient ![d, r, s] =
      (1 / d + 1 / r + 1 / s) ^ 2 / 2 - ((1 / d) ^ 2 + (1 / r) ^ 2 + (1 / s) ^ 2) / 4 := by
  simp [cubicParityCoefficient, parityCoefficient, centralWeight, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

theorem benchmark_cubic_mixed (d r₁ r₂ s₁ s₂ : ℚ) :
    cubicParityCoefficient ![d, r₁, s₁] - cubicParityCoefficient ![d, r₁, s₂] -
      cubicParityCoefficient ![d, r₂, s₁] + cubicParityCoefficient ![d, r₂, s₂] =
      (1 / r₁ - 1 / r₂) * (1 / s₁ - 1 / s₂) := by
  simp_rw [cubic_coefficient_three]
  ring

/-- The cubic-matched scalar coupling for retaining the three orbitals at `-d, 0, d`.
`a` is the sum of the removed reciprocal radii and `q` their squared sum. -/
def cubicMatchedCoupling (g a q : ℚ) : ℚ := g + g ^ 2 * a + g ^ 3 * (a ^ 2 - q / 2)

/-- Equating the two cubic parity coefficients uniquely fixes the coupling coefficient. -/
theorem cubic_coefficient_match_iff (u a q b : ℚ) :
    b / 2 + a * u + u ^ 2 / 4 = (u + a) ^ 2 / 2 - (u ^ 2 + q) / 4 ↔
      b = a ^ 2 - q / 2 := by
  constructor <;> intro h <;> linarith [mul_comm u a]

/-- Substitution into the retained parity polynomial matches the full parity through cubic
order. The difference is a multiple of `g⁴`. Here `u = 1/d`, `a = 1/r + 1/s`, and
`q = 1/r² + 1/s²`. -/
theorem cubic_match_remainder (g u a q : ℚ) :
    let b := a ^ 2 - q / 2
    let t := a + g * b
    let k := cubicMatchedCoupling g a q
    (k / 2 + k ^ 2 * u / 2 + k ^ 3 * u ^ 2 / 4) -
      (g / 2 + g ^ 2 * (u + a) / 2 + g ^ 3 * ((u + a) ^ 2 / 2 - (u ^ 2 + q) / 4)) =
      g ^ 4 * (b * u + t ^ 2 * u / 2 + t * (3 + 3 * g * t + g ^ 2 * t ^ 2) * u ^ 2 / 4) := by
  dsimp [cubicMatchedCoupling]
  ring

end Grain.ParityMatching
