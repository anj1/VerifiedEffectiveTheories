import Grain.HubbardChannels

/-! Identities for the channels and for the pair-removal resolvent. -/

namespace Grain.HubbardChannels

theorem momentum_parameterization (k l p r : Momentum) :
    (xor k l = xor p r) ↔
      ∃! q : Momentum, l = xor q k ∧ r = xor q p := by
  simp only [ExistsUnique]
  revert k l p r
  decide +kernel

def occupied (a : State) (k : Momentum) (down : Bool) : Bool :=
  a.val.testBit (slot k down).val

def totalMomentum (a : State) : Momentum :=
  momenta.foldl (fun q k => if occupied a k false != occupied a k true then xor q k else q) 0

def spinImbalance (a : State) : ℤ :=
  (momenta.countP fun k => occupied a k false : ℤ) -
    (momenta.countP fun k => occupied a k true : ℤ)

def sameSector (a b : State) : Bool :=
  totalMomentum a == totalMomentum b && spinImbalance a == spinImbalance b

def preservesSector (ops : List (Bool × Slot)) (a : State) : Bool :=
  match applyOps ops a with
  | some (b, _) => sameSector a b
  | none => true

def retainedSector (a : State) : Bool :=
  totalMomentum a == 0 && spinImbalance a == 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem scatter_preserves_sector (q k p : Momentum) (a : State) :
    preservesSector (scatter q k p) a = true := by
  revert a
  fin_cases q <;> fin_cases k <;> fin_cases p <;> decide +kernel

set_option maxRecDepth 10000 in
theorem source_preserves_sector (create : Bool) (k : Momentum) (a : State) :
    preservesSector (pairSource create k) a = true := by
  revert a
  cases create <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 10000 in
theorem retained_sector_size : ((List.finRange 256).filter retainedSector).length = 22 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem scatter_survives_elimination (q k p : Momentum) :
    ((List.finRange 256).filter retainedSector).any
      (fun a => (applyOps (scatter q k p) a).isSome) = true := by
  fin_cases q <;> fin_cases k <;> fin_cases p <;> decide +kernel

def spinFlip (k : Momentum) (down : Bool) : List (Bool × Slot) :=
  [(false, slot k (!down)), (true, slot k down)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem density_action (q k : Momentum) (a : State) :
    applyOps (scatter q k k) a =
      if occupied a k false && occupied a (xor q k) true then some (a, 1) else none := by
  revert a
  fin_cases q <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem exchange_action (k p : Momentum) (a : State) (hne : k ≠ p) :
    applyOps (scatter (xor k p) k p) a =
      (applyOps (spinFlip p true ++ spinFlip k false) a).map (fun (b, sign) => (b, -sign)) := by
  revert a hne
  fin_cases k <;> fin_cases p <;> decide +kernel

def pairs (a : State) : ℕ := momenta.countP (fun k => occupied a k false && occupied a k true)

def densityCount (a : State) : ℕ :=
  (momenta.flatMap (fun k => (momenta.filter fun l => k != l).map (k, ·))).countP
    (fun (k, l) => occupied a k false && occupied a l true)

set_option maxRecDepth 10000 in
theorem density_in_paired_block (a : State) (ha : blocked a = 0) :
    densityCount a = pairs a * (pairs a - 1) := by
  revert a ha
  decide +kernel

def filled : State := 255

def onePairHole (k : Momentum) : State := Fin.ofNat 256 (255 ^^^ (3 <<< (2*k.val)))

/-- Energies in fortieths of a meV for the isolated filled-state column. -/
def filledBinding (mask : Fin 8) : ℤ := if mask.val.testBit 0 then 240 else 60

set_option maxRecDepth 10000 in
theorem filled_column (mask : Fin 8) (i : State) :
    entry mask false i filled = if i = filled then -(filledBinding mask) else 0 := by
  revert i
  fin_cases mask <;> decide +kernel

set_option maxRecDepth 10000 in
theorem filled_source (i : State) :
    entry 7 true i filled - entry 7 false i filled =
      if i ∈ momenta.map onePairHole then -2 else 0 := by
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
theorem pair_hole_closed (k : Momentum) (i : State) (hi : i ∉ momenta.map onePairHole) :
    entry 7 false i (onePairHole k) = 0 := by
  revert i hi
  fin_cases k <;> decide +kernel

/-- The pair-removal block shifted by the filled-state energy, in meV. -/
def removalMatrix (k j : Momentum) : ℚ :=
  ((entry 7 false (onePairHole k) (onePairHole j) : ℚ) +
    (if k = j then 240 else 0)) / 40

theorem removal_entries (k j : Momentum) :
    removalMatrix k j = (if k = j then 3 - (levels k : ℚ) / 4 else 0) - 3/8 := by
  revert k j
  decide +kernel

def removalVector (k : Momentum) : ℚ :=
  15561 / (6609 * (3 - (levels k : ℚ) / 4))

/-- The response coefficient from the filled-state pair-removal resolvent.
The inverse action on the uniform source is checked directly. -/
theorem pair_removal_resolvent :
    (∀ k, action removalMatrix removalVector k = 1) ∧
    (∑ k, removalVector k) / 2 = 11936/6609 := by decide +kernel

end Grain.HubbardChannels
