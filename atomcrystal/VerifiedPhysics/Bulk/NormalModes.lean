import VerifiedPhysics.Atomistic.LinearDynamics

/-!
A second exact bulk geometry has two cells on a periodic ring. Its four axial
ionic displacements have masses six. Four nearest-neighbor harmonic bonds
each have spring three; at zero wave number their total relative spring is
six, agreeing with the one-cell optical model. The ring supports `k = 0` and
`k = π` only. This is finite normal-mode evidence, not an infinite-crystal
dispersion theorem.
-/

namespace VerifiedPhysics

abbrev TwoCellDisplacement := Fin 4 → ℝ

noncomputable def twoCellPotential (v : TwoCellDisplacement) : ℝ :=
  (3 / 2) * ((v 0 - v 2) ^ 2 + (v 0 - v 3) ^ 2 +
    (v 1 - v 2) ^ 2 + (v 1 - v 3) ^ 2)

noncomputable def twoCellOperator (v : TwoCellDisplacement) : TwoCellDisplacement :=
  fun i =>
    if i = 0 then v 0 - (v 2 + v 3) / 2
    else if i = 1 then v 1 - (v 2 + v 3) / 2
    else if i = 2 then v 2 - (v 0 + v 1) / 2
    else v 3 - (v 0 + v 1) / 2

theorem two_cell_energy_nonnegative (v : TwoCellDisplacement) :
    0 ≤ twoCellPotential v := by
  unfold twoCellPotential
  positivity

/-- The dynamical matrix is the mass-normalized quadratic form of the
specified ionic bond energy. -/
theorem two_cell_quadratic_bridge (v : TwoCellDisplacement) :
    twoCellPotential v = 3 * ∑ i : Fin 4, v i * twoCellOperator v i := by
  simp [twoCellPotential, twoCellOperator, Fin.sum_univ_four]
  ring

def acousticPattern : TwoCellDisplacement := ![1, 1, 1, 1]
def opticalPattern : TwoCellDisplacement := ![1, 1, -1, -1]
def zoneEdgeCationPattern : TwoCellDisplacement := ![1, -1, 0, 0]
def zoneEdgeAnionPattern : TwoCellDisplacement := ![0, 0, 1, -1]

theorem acoustic_mode_at_zero_wavevector :
    twoCellOperator acousticPattern = 0 := by
  funext i
  fin_cases i <;>
    norm_num [twoCellOperator, acousticPattern, Pi.zero_apply]

theorem optical_mode_at_zero_wavevector :
    twoCellOperator opticalPattern = 2 • opticalPattern := by
  funext i
  fin_cases i <;>
    norm_num [twoCellOperator, opticalPattern, Pi.smul_apply]

theorem cation_mode_at_zone_edge :
    twoCellOperator zoneEdgeCationPattern = zoneEdgeCationPattern := by
  funext i
  fin_cases i <;>
    norm_num [twoCellOperator, zoneEdgeCationPattern]

theorem anion_mode_at_zone_edge :
    twoCellOperator zoneEdgeAnionPattern = zoneEdgeAnionPattern := by
  funext i
  fin_cases i <;>
    norm_num [twoCellOperator, zoneEdgeAnionPattern]

end VerifiedPhysics
