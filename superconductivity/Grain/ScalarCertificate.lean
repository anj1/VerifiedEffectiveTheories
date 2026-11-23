import Grain.ScalarError
import Grain.ShellValidation

namespace Grain.ParityMatching

open ResolventRemainder

private def size (c : Fin 3) : ℕ := if c = 1 then 7 else 6

private def digits (code : ℕ) (i : Fin 3) : ℕ := code / 3^i.val % 3

private def codes (c : Fin 3) :=
  (List.range 27).filter fun code => (∑ i : Fin 3, digits code i) == 2 + c.val

private theorem codes_length (c : Fin 3) : (codes c).length = size c := by
  fin_cases c <;> decide +kernel

private def occ (c : Fin 3) (j : Fin (size c)) :=
  digits ((codes c)[j.val]'(by rw [codes_length]; exact j.isLt))

private def transfer (a b : Fin 3 → ℕ) : Prop :=
  ∃ i j : Fin 3, a i = 2 ∧ a j = 0 ∧
    ∀ k : Fin 3, b k = (if k = i then 0 else if k = j then 2 else a k)

private instance (a b : Fin 3 → ℕ) : Decidable (transfer a b) := by
  unfold transfer
  infer_instance

def rationalStrength (r s : Bool) : ℚ :=
  let x : ℚ := if r then 1/5 else 1/2
  let y : ℚ := if s then 1/14 else 1/6
  cubicMatchedCoupling (1/100) (x+y) (x^2+y^2)

theorem strength_cast (r s : Bool) : (rationalStrength r s : ℝ) = strength r s := by
  cases r <;> cases s <;>
    norm_num [rationalStrength, cubicMatchedCoupling, strength, inverseInner, inverseOuter]

def retainedH (r s : Bool) (c : Fin 3) (i j : Fin (size c)) : ℚ :=
  let a := occ c i
  let g := rationalStrength r s
  if i = j then (a 2 : ℚ) - a 0 - g * (∑ k : Fin 3, if a k = 2 then 1 else 0)
  else if transfer a (occ c j) then -g else 0

private structure Witness (c : Fin 3) where
  lo : ℚ
  hi : ℚ
  weight : Fin (size c) → ℚ
  trial : Fin (size c) → ℚ

private def witness : (r s : Bool) → (c : Fin 3) → Witness c
  | false, false, 0 => ⟨-201014323376246507/100000000000000000, -25126790422030813/12500000000000000, ![1000000000000000000000000, 1, 5046025373763826664670, 1, 1, 2529394380995292278688], ![1000000000000000000000000, 0, 5046025373763826664670, 0, 0, 2529394380995292278688]⟩
  | false, false, 1 => ⟨-100504615402208851/50000000000000000, -201009230804417699/100000000000000000, ![1000000000000000000000000, 1, 1, 1, 1, 1, 2516727114718038180362], ![1000000000000000000000000, 0, 0, 0, 0, 0, 2516727114718038180362]⟩
  | false, false, 2 => ⟨-202021020598468729/100000000000000000, -101010510299234363/50000000000000000, ![1000000000000000000000000, 1, 1, 5046025373763825564744, 1, 2529394380995291725939], ![1000000000000000000000000, 0, 0, 5046025373763825564744, 0, 2529394380995291725939]⟩
  | false, true, 0 => ⟨-100506672864881321/50000000000000000, -201013345729762639/100000000000000000, ![1000000000000000000000000, 1, 5041186325633119274701, 1, 1, 2526962607487686204868], ![1000000000000000000000000, 0, 5041186325633119274701, 0, 0, 2526962607487686204868]⟩
  | false, true, 1 => ⟨-50252065730201929/25000000000000000, -201008262920807713/100000000000000000, ![1000000000000000000000000, 1, 1, 1, 1, 1, 2514319564050556008077], ![1000000000000000000000000, 0, 0, 0, 0, 0, 2514319564050556008077]⟩
  | false, true, 2 => ⟨-12626192494589757/6250000000000000, -202019079913436109/100000000000000000, ![1000000000000000000000000, 1, 1, 5041186325633122305139, 1, 2526962607487687727755], ![1000000000000000000000000, 0, 0, 5041186325633122305139, 0, 2526962607487687727755]⟩
  | true, false, 0 => ⟨-40202251421319683/20000000000000000, -50252814276649603/25000000000000000, ![1000000000000000000000000, 1, 5030848128381857556409, 1, 1, 2521767378539197951865], ![1000000000000000000000000, 0, 5030848128381857556409, 0, 0, 2521767378539197951865]⟩
  | true, false, 1 => ⟨-40201239024754637/20000000000000000, -100503097561886591/50000000000000000, ![1000000000000000000000000, 1, 1, 1, 1, 1, 2509176007773686124206], ![1000000000000000000000000, 0, 0, 0, 0, 0, 2509176007773686124206]⟩
  | true, false, 2 => ⟨-202014933828820637/100000000000000000, -101007466914410317/50000000000000000, ![1000000000000000000000000, 1, 1, 5030848128381856456450, 1, 2521767378539197399107], ![1000000000000000000000000, 0, 0, 5030848128381856456450, 0, 2521767378539197399107]⟩
  | true, true, 0 => ⟨-20101028530484119/10000000000000000, -201010285304841187/100000000000000000, ![1000000000000000000000000, 1, 5026037863231956697078, 1, 1, 2519350106128046854512], ![1000000000000000000000000, 0, 5026037863231956697078, 0, 0, 2519350106128046854512]⟩
  | true, true, 1 => ⟨-25125654124705167/12500000000000000, -201005232997641333/100000000000000000, ![1000000000000000000000000, 1, 1, 1, 1, 1, 2506782742277202797027], ![1000000000000000000000000, 0, 0, 0, 0, 0, 2506782742277202797027]⟩
  | true, true, 2 => ⟨-101006502351400187/50000000000000000, -202013004702800371/100000000000000000, ![1000000000000000000000000, 1, 1, 5026037863231958313361, 1, 2519350106128047666731], ![1000000000000000000000000, 0, 0, 5026037863231958313361, 0, 2519350106128047666731]⟩

noncomputable def retainedParity (r s : Bool) : ℝ :=
  ground (retainedH r s 1) - (ground (retainedH r s 0) + ground (retainedH r s 2)) / 2

private def Valid (r s : Bool) (c : Fin 3) : Prop :=
  let A := retainedH r s c
  let w := witness r s c
  (∀ i j, A i j = A j i) ∧ (∀ i j, i ≠ j → A i j ≤ 0) ∧
  (∀ i, 0 < w.weight i) ∧ (∀ i, w.lo * w.weight i ≤ action A w.weight i) ∧
  0 < rationalNormSq w.trial ∧ rayleighNumerator A w.trial ≤ w.hi * rationalNormSq w.trial

private instance (r s : Bool) (c : Fin 3) : Decidable (Valid r s c) := by
  unfold Valid
  infer_instance

set_option maxHeartbeats 0 in
private theorem valid (r s : Bool) (c : Fin 3) : Valid r s c := by
  cases r <;> cases s <;> fin_cases c <;> decide +kernel

private theorem sector (r s : Bool) (c : Fin 3) :
    ((witness r s c).lo : ℝ) ≤ ground (retainedH r s c) ∧
    ground (retainedH r s c) ≤ ((witness r s c).hi : ℝ) := by
  obtain ⟨hs, hn, hw, hl, ht, hu⟩ := valid r s c
  exact ground_bounds _ _ _ (weighted_lower _ _ _ hs hn hw hl) (normalized_trial _ _ ht _ hu)

private def parityLo (r s : Bool) : ℚ :=
  (witness r s 1).lo - ((witness r s 0).hi + (witness r s 2).hi) / 2

private def parityHi (r s : Bool) : ℚ :=
  (witness r s 1).hi - ((witness r s 0).lo + (witness r s 2).lo) / 2

private theorem parity (r s : Bool) :
    (parityLo r s : ℝ) ≤ retainedParity r s ∧ retainedParity r s ≤ (parityHi r s : ℝ) := by
  obtain ⟨l₀, u₀⟩ := sector r s 0
  obtain ⟨l₁, u₁⟩ := sector r s 1
  obtain ⟨l₂, u₂⟩ := sector r s 2
  push_cast [parityLo, parityHi]
  unfold retainedParity
  constructor <;> linarith

theorem retained_benchmark_polynomial_error (r s : Bool) :
    |retainedParity r s - retainedPolynomial r s| ≤
      2 * budget 2 (strength r s) 2 2 := by
  obtain ⟨hl, hu⟩ := parity r s
  rw [abs_le]
  cases r <;> cases s <;>
    norm_num [parityLo, parityHi, witness, retainedPolynomial, strength,
      inverseInner, inverseOuter, budget] at hl hu ⊢ <;>
    constructor <;> linarith

theorem benchmark_analytic_error :
    |TwoShell.Prediction.mixedContrast - mixed retainedParity| ≤ 204 / 10^7 :=
  benchmark_scalar_error_of_retained retainedParity retained_benchmark_polynomial_error

/-- The frozen nested reduction and the scalar control already resolve the
signed discrepancy before using the independent full solve. -/
theorem benchmark_reduced_error :
    2025 / 10^13 ≤ TwoShell.Prediction.mixedContrast - mixed retainedParity ∧
    TwoShell.Prediction.mixedContrast - mixed retainedParity ≤ 2030 / 10^13 := by
  obtain ⟨lf, uf⟩ := TwoShell.Prediction.mixed_bounds
  rw [TwoShell.Prediction.mixed_endpoints.1] at lf
  rw [TwoShell.Prediction.mixed_endpoints.2.2] at uf
  obtain ⟨la, ua⟩ := parity false false
  obtain ⟨lb, ub⟩ := parity false true
  obtain ⟨lc, uc⟩ := parity true false
  obtain ⟨ld, ud⟩ := parity true true
  norm_num [parityLo, parityHi, witness, mixed] at *
  constructor <;> linarith

/-- Signed discrepancy from the independent full solve, in spacing units. -/
theorem benchmark_sharp_error :
    2027478 / 10^16 ≤ TwoShell.Prediction.mixedContrast - mixed retainedParity ∧
    TwoShell.Prediction.mixedContrast - mixed retainedParity ≤ 2027483 / 10^16 := by
  obtain ⟨lf, uf⟩ := TwoShell.FullSolve.mixed_bounds
  rw [TwoShell.FullSolve.full_endpoints.1] at lf
  rw [TwoShell.FullSolve.full_endpoints.2] at uf
  obtain ⟨la, ua⟩ := parity false false
  obtain ⟨lb, ub⟩ := parity false true
  obtain ⟨lc, uc⟩ := parity true false
  obtain ⟨ld, ud⟩ := parity true true
  norm_num [parityLo, parityHi, witness, mixed] at *
  constructor <;> linarith

end Grain.ParityMatching
