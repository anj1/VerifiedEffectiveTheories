import VerifiedPhysics.Base.Model

/-!
Finite staggered transverse-magnetic Maxwell model. There are sixteen
magnetic cells on each side of the interface, cell width 1/8, and squared
parallel wave number 6. Tangential E vanishes at both outer boundaries.
Material electric degrees of freedom carry explicit ionic pairs, with mass
6 per ion, charge ±3, and reduced mass 3. The interface dual cell is half
filled. `b` is the mass-normalized local ionic stiffness.

The scalar dielectric factors below are eliminated coordinates, not input
to the primitive ionic-Maxwell equations defined later in this file.
-/

namespace VerifiedPhysics.MaxwellSlab

noncomputable def eps (b s : ℝ) : ℝ := 1 + 3 / (b - s)
noncomputable def epsInterface (b s : ℝ) : ℝ := 1 + (3 / 2 : ℝ) / (b - s)

/-- Homogeneous half-slab profile, indexed from its conducting outer face.
The first recurrence is precisely the zero tangential-E outer condition. -/
noncomputable def profile (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => q - 1
  | n + 2 => q * profile q (n + 1) - profile q n

noncomputable def qVac (s : ℝ) : ℝ := 2 + (6 - s) / 64
noncomputable def qMat (b s : ℝ) : ℝ := 2 + (6 - eps b s * s) / 64
noncomputable def interfaceCoupling (b s : ℝ) : ℝ := 64 / epsInterface b s
noncomputable def leftResidual (b s : ℝ) : ℝ :=
  (64 + 6 - s + interfaceCoupling b s) * profile (qVac s) 15 -
    64 * profile (qVac s) 14
noncomputable def rightResidual (b s : ℝ) : ℝ :=
  (64 / eps b s + 6 / eps b s - s + interfaceCoupling b s) *
    profile (qMat b s) 15 - (64 / eps b s) * profile (qMat b s) 14
noncomputable def characteristic (b s : ℝ) : ℝ :=
  leftResidual b s * rightResidual b s -
    interfaceCoupling b s ^ 2 * profile (qVac s) 15 * profile (qMat b s) 15

/-- Real TM Fourier amplitudes on the finite staggered grid. Normal electric
and ionic amplitudes are divided by the parallel wave number `sqrt 6`.
Only indices 0..15 (cells) and 0..14 (internal faces) enter the model. -/
structure Fields where
  vacuumH : ℕ → ℝ
  materialH : ℕ → ℝ
  vacuumE : ℕ → ℝ
  materialE : ℕ → ℝ
  normalE : ℕ → ℝ
  tangentialIon : ℕ → ℝ
  normalIon : ℕ → ℝ
  interfaceE : ℝ
  interfaceIon : ℝ

/-- Primitive finite Maxwell-ion equations. Ionic variables have not been
eliminated and the definition contains no dielectric law. These are the
two discrete curl equations with explicit polarization `P=3u`, the ionic
Newton equation, and conducting outer-face conditions. -/
def MaxwellIonMode (b s : ℝ) (f : Fields) : Prop :=
  0 < f.vacuumH 15 ^ 2 + f.materialH 15 ^ 2 ∧
  (∀ j < 16, f.normalE j + 3 * f.normalIon j = f.materialH j ∧
    (b - s) * f.normalIon j = f.normalE j) ∧
  (∀ j < 15,
    f.vacuumE j = 8 * (f.vacuumH (j+1) - f.vacuumH j) ∧
    f.materialE j + 3 * f.tangentialIon j =
      8 * (f.materialH (j+1) - f.materialH j) ∧
    (b - s) * f.tangentialIon j = f.materialE j) ∧
  f.interfaceE + (3 / 2 : ℝ) * f.interfaceIon =
    8 * (f.vacuumH 15 - f.materialH 15) ∧
  (b - s) * f.interfaceIon = f.interfaceE ∧
  -8 * f.vacuumE 0 + 6 * f.vacuumH 0 = s * f.vacuumH 0 ∧
  -8 * f.materialE 0 + 6 * f.normalE 0 = s * f.materialH 0 ∧
  (∀ j < 14,
    8 * (f.vacuumE j - f.vacuumE (j+1)) + 6 * f.vacuumH (j+1) =
      s * f.vacuumH (j+1) ∧
    8 * (f.materialE j - f.materialE (j+1)) + 6 * f.normalE (j+1) =
      s * f.materialH (j+1)) ∧
  8 * (f.vacuumE 14 + f.interfaceE) + 6 * f.vacuumH 15 = s * f.vacuumH 15 ∧
  8 * (f.materialE 14 - f.interfaceE) + 6 * f.normalE 15 = s * f.materialH 15

/-- Magnetic equation obtained by eliminating electric and ionic variables.
This predicate is auxiliary; the final theorem asserts `MaxwellIonMode`. -/
def MagneticMode (b s : ℝ) (v m : ℕ → ℝ) : Prop :=
  0 < v 15 ^ 2 + m 15 ^ 2 ∧
  (70 - s) * v 0 - 64 * v 1 = 0 ∧
  (70 - eps b s * s) * m 0 - 64 * m 1 = 0 ∧
  (∀ j < 14,
    (134 - s) * v (j+1) - 64 * v j - 64 * v (j+2) = 0 ∧
    (134 - eps b s * s) * m (j+1) - 64 * m j - 64 * m (j+2) = 0) ∧
  (70 - s + interfaceCoupling b s) * v 15 - 64 * v 14 -
    interfaceCoupling b s * m 15 = 0 ∧
  (70 - eps b s * s + eps b s * interfaceCoupling b s) * m 15 - 64 * m 14 -
    eps b s * interfaceCoupling b s * v 15 = 0

noncomputable def reconstruct (b s : ℝ) (v m : ℕ → ℝ) : Fields where
  vacuumH := v
  materialH := m
  vacuumE := fun j => 8 * (v (j+1) - v j)
  materialE := fun j => 8 * (m (j+1) - m j) / eps b s
  normalE := fun j => m j / eps b s
  tangentialIon := fun j => (8 * (m (j+1) - m j) / eps b s) / (b - s)
  normalIon := fun j => (m j / eps b s) / (b - s)
  interfaceE := 8 * (v 15 - m 15) / epsInterface b s
  interfaceIon := (8 * (v 15 - m 15) / epsInterface b s) / (b - s)

theorem profile_step (q : ℝ) (n : ℕ) :
    profile q (n+2) = q * profile q (n+1) - profile q n := rfl

theorem profile_positive_mono (q : ℝ) (hq : 2 ≤ q) (n : ℕ) :
    1 ≤ profile q n ∧ profile q n ≤ profile q (n+1) := by
  induction n with
  | zero => simp only [profile]; constructor <;> linarith
  | succ n ih =>
    rw [show n+1+1=n+2 by omega, profile_step]
    constructor
    · linarith [ih.1, ih.2]
    · nlinarith [ih.1, ih.2, mul_nonneg (by linarith : 0 ≤ q-2)
        (by linarith [ih.1, ih.2] : 0 ≤ profile q (n+1))]

noncomputable def vacuumWitness (b s : ℝ) (j : ℕ) : ℝ :=
  interfaceCoupling b s * profile (qMat b s) 15 * profile (qVac s) j
noncomputable def materialWitness (b s : ℝ) (j : ℕ) : ℝ :=
  leftResidual b s * profile (qMat b s) j

theorem root_magnetic_mode (b s : ℝ)
    (he : eps b s ≠ 0) (hi : epsInterface b s ≠ 0)
    (hqv : 2 ≤ qVac s) (hqm : 2 ≤ qMat b s)
    (hroot : characteristic b s = 0) :
    MagneticMode b s (vacuumWitness b s) (materialWitness b s) := by
  have hv : 0 < profile (qVac s) 15 := lt_of_lt_of_le (by norm_num) (profile_positive_mono _ hqv 15).1
  have hm : 0 < profile (qMat b s) 15 := lt_of_lt_of_le (by norm_num) (profile_positive_mono _ hqm 15).1
  have hc : interfaceCoupling b s ≠ 0 := div_ne_zero (by norm_num) hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn : vacuumWitness b s 15 ≠ 0 := mul_ne_zero (mul_ne_zero hc (ne_of_gt hm)) (ne_of_gt hv)
    nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (materialWitness b s 15)]
  · dsimp [vacuumWitness, profile, qVac]; ring
  · dsimp [materialWitness, profile, qMat]; ring
  · intro j _
    constructor
    · dsimp [vacuumWitness]
      rw [profile_step (qVac s) j]
      unfold qVac
      ring
    · dsimp [materialWitness]
      rw [profile_step (qMat b s) j]
      unfold qMat
      ring
  · dsimp [vacuumWitness, materialWitness, leftResidual]
    ring
  · have hid :
        (70 - eps b s * s + eps b s * interfaceCoupling b s) * materialWitness b s 15 -
          64 * materialWitness b s 14 - eps b s * interfaceCoupling b s * vacuumWitness b s 15 =
        eps b s * characteristic b s := by
      unfold vacuumWitness materialWitness characteristic rightResidual
      field_simp [he]
      ring
    rw [hid, hroot]
    ring

end VerifiedPhysics.MaxwellSlab
