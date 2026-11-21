import Grain.CrystalBCS

/-! The signed Fock Hamiltonian of the four-site example in momentum space. -/

namespace Grain.HubbardChannels

abbrev Momentum := Fin 4
abbrev State := Fin 256
abbrev Slot := Fin 8

def xor (k p : Momentum) : Momentum := Fin.ofNat 4 (k.val ^^^ p.val)

def slot (k : Momentum) (down : Bool) : Slot :=
  ⟨2 * k.val + down.toNat, by have := k.isLt; cases down <;> simp_all <;> omega⟩

def walsh (a k : Momentum) : ℤ :=
  (-1) ^ ((a.val &&& k.val).testBit 0).toNat * (-1) ^ ((a.val &&& k.val).testBit 1).toNat

/-- Before the four factors of 1/2 from the normalized Fourier orbitals. -/
theorem site_vertex_fourier (k l p r : Momentum) :
    (∑ a : Momentum, walsh a k * walsh a l * walsh a p * walsh a r) =
      if xor k l = xor p r then 4 else 0 := by
  revert k l p r
  decide +kernel

/-- Before the two factors of 1/2 in the uniform pair source. -/
theorem site_source_fourier (k l : Momentum) :
    (∑ a : Momentum, walsh a k * walsh a l) = if k = l then 4 else 0 := by
  revert k l
  decide +kernel

inductive Channel
  | cooper | density | exchange | fourMomenta
  deriving DecidableEq

def channel (q k p : Momentum) : Channel :=
  if q = 0 then .cooper else if k = p then .density else
    if xor k p = q then .exchange else .fourMomenta

theorem distinct_momenta (q k p : Momentum) :
    (channel q k p = .fourMomenta) ↔
      q ≠ 0 ∧ ([k, xor q k, p, xor q p]).Nodup := by
  revert q k p
  decide +kernel

/-- One creation or annihilation in the interleaved up/down Fock order. -/
def step (create : Bool) (s : Slot) (state : State) : Option (State × ℤ) :=
  if state.val.testBit s.val == create then none
  else
    let sign : ℤ := (-1) ^ ((List.range s.val).countP state.val.testBit)
    some (Fin.ofNat 256 (state.val ^^^ 2 ^ s.val), sign)

/-- The list lists operators in their order of application. -/
def applyOps : List (Bool × Slot) → State → Option (State × ℤ)
  | [], a => some (a, 1)
  | (create, s) :: rest, a => do
    let (b, sign) ← step create s a
    let (c, restSign) ← applyOps rest b
    return (c, sign * restSign)

def scatter (q k p : Momentum) : List (Bool × Slot) :=
  [(false, slot p false), (false, slot (xor q p) true),
    (true, slot (xor q k) true), (true, slot k false)]

def pairSource (create : Bool) (k : Momentum) : List (Bool × Slot) :=
  if create then [(true, slot k true), (true, slot k false)]
  else [(false, slot k false), (false, slot k true)]

def blocked (a : State) : ℕ :=
  ((a.val ^^^ (a.val >>> 1)) &&& 85)

def preservesBlocked (kind : Channel) (q k p : Momentum) (a : State) : Bool :=
  if channel q k p != kind then true
  else match applyOps (scatter q k p) a with
  | none => true
  | some (b, _) => if kind = .fourMomenta then blocked a ^^^ blocked b == 85
      else blocked a == blocked b

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem scattering_blocked (q k p : Momentum) (a : State) :
    preservesBlocked (channel q k p) q k p a = true := by
  revert a
  fin_cases q <;> fin_cases k <;> fin_cases p <;> decide +kernel

/-- Energies in eighths of a meV for the site example, after the static shift. -/
def levels : Momentum → ℤ := ![-7, 3, -1, 5]

/-- The numerator of the one-body Fourier transform before orbital normalization.
The diagonal hopping includes the static shift and chemical potential. -/
def hopping : Momentum → ℤ := ![0, -4, -2, -1]

theorem site_kinetic_fourier (k p : Momentum) :
    (∑ a : Momentum, ∑ b : Momentum, walsh a k * hopping (xor a b) * walsh b p) =
      if k = p then 4 * levels k else 0 := by
  revert k p
  decide +kernel

/-- The mask bits retain density, exchange, and scattering at four distinct momenta. -/
def retained (mask : Fin 8) : Channel → Bool
  | .cooper => true
  | .density => mask.val.testBit 0
  | .exchange => mask.val.testBit 1
  | .fourMomenta => mask.val.testBit 2

def momenta : List Momentum := List.finRange 4

def interactions (mask : Fin 8) : List (List (Bool × Slot)) :=
  momenta.flatMap fun q => momenta.flatMap fun k =>
    (momenta.filter fun p => retained mask (channel q k p)).map (scatter q k)

def sources : List (List (Bool × Slot)) :=
  momenta.flatMap fun k => [pairSource true k, pairSource false k]

/-- Hamiltonian entries are scaled by 40, so the field 1/20 and attraction
3/8 both have integer coefficients. Each list is one column of the matrix. -/
def column (mask : Fin 8) (field : Bool) (a : State) : List (State × ℤ) :=
  let kinetic := (momenta.map fun k => 5 * levels k *
    ((a.val.testBit (slot k false).val).toNat + (a.val.testBit (slot k true).val).toNat : ℤ)).sum
  let terms := (interactions mask).map (fun ops => (ops, (-15 : ℤ))) ++
    (if field then sources.map (fun ops => (ops, (-2 : ℤ))) else [])
  (a, kinetic) :: terms.filterMap (fun (ops, coefficient) =>
    (applyOps ops a).map fun (b, sign) => (b, coefficient * sign))

def entry (mask : Fin 8) (field : Bool) (i j : State) : ℤ :=
  ((column mask field j).map fun (k, v) => if k = i then v else 0).sum

end Grain.HubbardChannels
