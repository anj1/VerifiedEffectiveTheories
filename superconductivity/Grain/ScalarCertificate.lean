import Grain.ScalarError
import Grain.ShellValidation

namespace Grain.ParityMatching

open ResolventRemainder

private structure Witness (c : Fin 3) where
  lo : ℚ
  hi : ℚ
  weight : Fin (retainedSize c) → ℚ
  trial : Fin (retainedSize c) → ℚ

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

/-- The analytic budget and the nested-reduction certificate use the same full matrix. -/
theorem fullParity_eq_prediction (r s : Bool) :
    fullParity r s = TwoShell.Prediction.parityEnergy r s := rfl

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
