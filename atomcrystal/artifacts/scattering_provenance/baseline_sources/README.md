# Atomcrystal: a verified finite ionic–Maxwell research loop

The strongest result is now
`verified_cross_scale_maxwell_surface_prediction` in
[Final/MainTheorem.lean](VerifiedPhysics/Final/MainTheorem.lean).
It connects the second derivative of the nonlinear ionic potential to an
explicit finite Maxwell–ion eigenmode, with a nonzero discrepancy from the
bulk-derived continuum prediction.

The effective theory predicts squared frequency `s=3` at `k²=6`.
For every declared uniform microscopic bias `|a|≤10⁻⁹`, Lean proves that the
independently specified finite Maxwell–ion system has a mode satisfying:

- `3.01 ≤ ω_micro² ≤ 3.012`;
- `0 < ω_micro - √3 ≤ 1/250`;
- at least `3/5` of its **magnetic-field energy** lies within distance one of
  the interface, in a box extending to distance two on each side;
- the squared-frequency error lies inside the preregistered `±3/100` budget.

The frequency enclosure is uniform over the microscopic Hessian interval.
It concerns infinitesimal modes about force-balanced equilibria. It does not
assert a finite-amplitude nonlinear oscillation frequency.

## The verified connections

[AxialForce.lean](VerifiedPhysics/Atomistic/AxialForce.lean) proves that the
nonlinear pair force differs from the harmonic force by at most
`40C|x|²` on `|x|≤1/2`, with `C=9/(4π)`.
[BiasedHessian.lean](VerifiedPhysics/Atomistic/BiasedHessian.lean) then derives
the **actual second derivative** of the nonlinear potential:
`b(a) = [6-C+C(1-2a)/(1+a)^4]/3`.
It proves equilibrium after the explicitly declared constant balancing force,
and bounds `b(a)` inside `[1.999999,2.000001]`.
The surface operator in the final theorem uses this second derivative
directly as its ionic coefficient.

[BiasedResponse.lean](VerifiedPhysics/Bulk/BiasedResponse.lean) derives the
ionic susceptibility from that Hessian. The unstrained response is exactly
`ε(s)=(5-s)/(2-s)`. On `3.01≤s≤3.012`, the strained microscopic response
obeys the deterministic constitutive bound
`|P_micro-(ε(s)-1)E|≤(3/10⁶)|E|`.

[TMFields.lean](VerifiedPhysics/Effective/TMFields.lean) constructs exponential
fields satisfying the differential TM Maxwell equations and the interface
conditions. [Reststrahlen.lean](VerifiedPhysics/Effective/Reststrahlen.lean)
proves unit reflected intensity for the lossless effective half-space on
`2<s<5`, using explicit reflection amplitudes and boundary equations.

The new lower-level calculation is a separate staggered Maxwell model:
32 magnetic cells, 63 electric amplitudes, and 32 physical ionic pairs.
[MaxwellSlab.lean](VerifiedPhysics/Atomistic/MaxwellSlab.lean) states the
primitive field and ionic equations without importing the effective theory.
[MaxwellHamiltonian.lean](VerifiedPhysics/Atomistic/MaxwellHamiltonian.lean)
specifies the finite curl matrix and nonlinear field–ion Hamiltonian, and
proves closed-system energy balance.
[HamiltonianBridge.lean](VerifiedPhysics/CrossScale/HamiltonianBridge.lean)
checks the ionic force against the coupled potential.

The surface certificate first encloses a root of the finite transfer
equations by rational inequalities and the intermediate value theorem.
It reconstructs the electric fields and ionic displacements, and checks them
against the explicit curl matrix and its transpose. Positive-coefficient
polynomial witnesses are checked against the transfer recurrence by Lean;
no numerical eigensolver is trusted.
The localization inequality is proved from the spatial profile.

## What is assumed

This is a dimensionless **polar-dimer crystal with a finite electromagnetic
mode basis**, not a calibrated NaCl model. Each physical pair has ion masses
6, charges ±3, and the original three-dimensional Coulomb-plus-short-range
potential. Pair centres are fixed lattice sites; translation modes are
excluded. The transverse force vanishes on the retained axial slice, as
checked in [AxialSlice.lean](VerifiedPhysics/Atomistic/AxialSlice.lean).
The dipoles couple to the selected polarization of the field.

Intercell coupling is through the retained Maxwell fields. Direct
short-range forces between different pairs, electronic polarizability,
damping, and thermal sampling are absent. The field spacing is `1/8`,
the outer faces are conducting, and the parallel Fourier wave number is
`√6`. Full material sites have field overlap one. The interface has
overlap `1/√2`: it contains a complete pair with unchanged masses and
charges.

The embedding into continuous three-dimensional particle positions and
momenta, including the exact kinetic energy and site geometry, is checked in
[Embedding.lean](VerifiedPhysics/Atomistic/Embedding.lean).

The Hamiltonian is explicitly
`Σ(D-3gu)²/2 + ΣH²/2 + Σ_occupied[p²/6+U(a+u)-U(a)-U′(a)u]`.
All new configuration assumptions are recorded in
[artifacts/maxwell_model.json](artifacts/maxwell_model.json).
The Lean definitions are normative. There is no claimed correspondence to
experimental NaCl, nor a general convergence theorem for arbitrary grids.

## Predictions, failures, and provenance

The original two-layer electrostatic surrogate is preserved. Its first
planar prediction fails with a certified squared-frequency discrepancy
strictly between `1/2` and `3/5`. Its corrected withheld `k²=12` prediction
has zero discrepancy within that same harmonic operator family.
Those earlier theorems remain available.

The new Maxwell experiment also preserves a failed attempt. The initial
eight-cells-per-side grid, spacing `1/4`, produced a candidate root in
`(3.04,3.05)`, outside its proposed `[2.97,3.03]` interval. This is retained
as an **empirical failure indication**; equal endpoint determinant signs
alone are not a proof that every root is absent from the prediction interval.

The next prediction explicitly halved the spacing and doubled the cell
count while keeping the domain and the `±0.03` prediction budget fixed.
The numerical root was approximately `3.0108887399619833`. Lean subsequently
certified the broader interval `[3.01,3.012]`, including the whole microscopic
stiffness uncertainty. See:

- [initial prediction](artifacts/maxwell_prediction.json) and
  [retained coarse result](artifacts/maxwell_coarse_result.json);
- [refined prediction](artifacts/maxwell_refined_prediction.json) and
  [refined result and error budget](artifacts/maxwell_refined_result.json).

[MaxwellPrediction.lean](VerifiedPhysics/Effective/MaxwellPrediction.lean)
imports no surface operator or surface certificate. Conversely, the numerical
surface certificate imports no effective dielectric theory. The read-only
audit checks both dependency closures. The execution artifacts record when
predictions were made; Lean does not prove a historical wall-clock ordering.
Source hashes identify the exact snapshot being verified.

## Trust status

| Artifact | Status |
| --- | --- |
| Hamiltonian, field basis, masses, charges, boundaries, bias domain | Assumption defining the finite model |
| Bulk samples and floating-point surface frequency | Empirical observation |
| Frozen prediction intervals before validation | Hypothesis |
| Transfer-polynomial identities and rational endpoint bounds | Certified computation checked inside Lean |
| Susceptibility, Maxwell reconstruction, localization, final discrepancy | Formal theorem |
| Applicability to real NaCl or to other geometries | Unestablished; no such claim is made |

The combined surface error is bounded uniformly over the declared microscopic
Hessian interval. There is no statistical combination of uncertainties.
Arithmetic certificate error is zero. The bulk constitutive error is
`3×10⁻⁶|E|`; the total frequency discrepancy for this finite experiment is
at most `0.004`. These bounds do not quantify material-model error against
experimental reality.

## Reproduce and independently verify

Use the pinned Lean 4.34.1 toolchain, then run from `atomcrystal/`:

```sh
lake update
lake exe cache get
lake build
lake env leanchecker VerifiedPhysics.Final.MainTheorem
lake build VerifiedPhysics.Final.Audit
python3 scripts/audit.py
python3 scripts/research.py bulk
python3 scripts/maxwell_slab.py --prediction artifacts/maxwell_prediction.json
python3 scripts/maxwell_slab.py --prediction artifacts/maxwell_refined_prediction.json
```

The independent verifier needs the Lean source and its pinned dependencies,
not the simulation scripts. The import audit and
[artifacts/source_revision.sha256](artifacts/source_revision.sha256) identify
the checked artifact set. No admitted proofs, project-specific axioms,
native proof shortcuts, or externally trusted numerical certificates are used.

The grating-coupling proposal remains a separate effective-theory result.
An atomistic scattering resonance and correspondence to real NaCl are outside
the proved finite-model claim.
