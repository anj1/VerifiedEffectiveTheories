# Atomcrystal: verified automated surface physics

This project closes a finite-model research loop from a nonlinear microscopic
ionic potential to a **withheld, momentum-matched driven-response experiment**.
The headline theorem is
[`verified_automated_surface_physics`](VerifiedPhysics/Final/MainTheorem.lean).
It combines a derived bulk constitutive law, a continuum TM surface prediction,
a certified finite ionic–Maxwell eigenmode, a theory-selected coupling geometry,
and independently generated, exactly checked driven field/ion solutions.

The experimental observable is **interface magnetic-field enhancement under a
prescribed periodic source**, not reflectivity. This deliberately uses the
finite driven-response alternative to open-boundary scattering. The coupler is
an ideal impressed magnetic source sheet (a patterned transducer); no claim of
passive-grating conversion efficiency is made.

## Lowest-level assumptions

The material is a dimensionless **finite polar-dimer ionic crystal with
Coulomb-plus-short-range interactions**, linearized about stable equilibrium.
It is not a calibrated model of real NaCl. Each of 32 pairs has masses 6 and 6,
charges +3 and −3, reference separation 1 and reduced mass 3. Pair centers are
fixed; the retained ionic coordinates are axial optical displacements.
Interpair coupling is through the retained Maxwell fields.

The microscopic potential, for relative coordinate r and C = 9/(4π), is

```text
U(r) = −C/|r| + C/(2|r|²) + (6−C)(|r|−1)²/2 + 3(r_x²+r_y²).
```

[NonlinearPotential](VerifiedPhysics/Atomistic/NonlinearPotential.lean)
proves mechanical stability on the collision-free domain.
[BiasedHessian](VerifiedPhysics/Atomistic/BiasedHessian.lean) proves that the
actual Hessian divided by reduced mass equals

```text
b(a) = [6−C + C(1−2a)/(1+a)^4]/3,     b(0) = 2.
```

Bias a is maintained by an explicitly specified constant balancing force.
The earlier eigenmode and bulk-error theorems allow |a| ≤ 10⁻⁹; the **new
driven-response certificate is at a = 0**. The axial force remainder obeys
|U′(u)−6u| ≤ 40C|u|² on |u| ≤ 1/2. This is a force estimate, not a nonlinear
trajectory or nonlinear frequency theorem.

The electromagnetic model has 32 magnetic cells, 63 electric amplitudes,
spacing 1/8, vacuum and material extending distance 2 on either side of the
interface, and conducting exterior faces. The retained parallel Fourier
wave number is √6. Exactly 32 occupied electric sites carry 64 physical ions.
The interface pair has overlap 1/√2, with unchanged masses and charges.
The explicit curl matrix, physical embedding, nonlinear Hamiltonian and
closed-system energy balance are retained from the earlier result.

## Automated discovery history

1. Bulk response yielded ε(s) = (5−s)/(2−s), where s = ω².
2. The initial planar/coarse two-layer prediction was falsified: its certified
   squared-frequency discrepancy lies strictly between 1/2 and 3/5.
3. A finite-slab correction predicted a withheld k² = 12 test successfully
   within that earlier harmonic family.
4. The first coarse Maxwell grid produced an empirical failure indication
   near s = 3.04–3.05. It remains an empirical indication, not a theorem
   excluding every root in the predicted interval.
5. The refined Maxwell prediction retained the ±0.03 budget and independently
   passed: s_micro ∈ [3.01, 3.012], with nonzero ionic participation and
   at least 60% near-interface magnetic localization.
6. The effective theory identified the next uncovered observable: excitation
   of the surface field. Direct vacuum incidence cannot supply √6 parallel
   momentum anywhere in the frozen s-window [2.97, 3.03].
7. The deterministic design rule selected normal incidence, the smallest
   positive diffraction order m = 1, and period Λ = 2π/√6. An ideal patterned
   source supplies cos(√6 x) from a spatially uniform incident channel.
8. **Before the first driven solve**, the source geometry, s_drive = 3,
   s_control = 4, prediction window, minimum intensity 1 and minimum intensity
   ratio 4 were frozen and hashed.
9. A separate rational finite Maxwell–ion solve passed that test. Lean checked
   the primitive equations, localization, nonzero ionic response and uniqueness
   of both measured interface amplitudes.

The previous failures and all existing theorems are preserved. The baseline
sources and README are also retained verbatim under
[baseline_sources](artifacts/scattering_provenance/baseline_sources).
The new experiment tests coupling and response; it does not pretend that the
previously known eigenfrequency itself was withheld again.

## Final verified result

Let C be the finite curl matrix, g_i the field overlaps, and u_i the physical
ionic displacement amplitudes. For each driven test the certificate proves

```text
C E = s H + J,       Cᵀ H = E + 3 g u,       (b−s)u = g E,
b = U_balanced″(0)/3 = 2,
J_15 = 1; all other magnetic source rows are zero.
```

The fully expanded matrix statement is
[`verified_driven_ionic_maxwell_equations`](VerifiedPhysics/CrossScale/GratingCorrespondence.lean).
The source is periodic with Λ and has nonzero matched Fourier amplitude.
Momentum matching is exact:

```text
√s sin θ < √6                         for all θ, 2.97 ≤ s ≤ 3.03,
√3 sin 0 + 1·(2π/Λ) = √6.
```

Define I(s) = H_vacuum(15)² + H_material(15)² for the unit generalized
source. This is the sum of squared magnetic amplitudes in the two
interface-adjacent cells; it is proportional to their magnetic energy.
The theorem proves

```text
I(3) ≥ 1,     I(4) ≤ 1/4,
I(3) ≥ 4 I(4),     I(3) − I(4) ≥ 3/4.
```

These inequalities hold for **every solution** of the primitive equations
at the respective frequency: exact adjoint certificates fix both measured
interface amplitudes. Rational witnesses separately prove existence.
At s = 3 the ionic response is nonzero and at least 60% of magnetic intensity
lies within distance 1 of the interface.

The associated finite eigenmode still satisfies

```text
3.01 ≤ ω_micro² ≤ 3.012 ⊂ [2.97, 3.03],
0 < ω_micro − √3 ≤ 0.004.
```

The interval containment and deterministic budget arithmetic are Lean
theorems. The drive point is √3; the distinct finite eigenfrequency is
ω_micro. We certify enhanced response at the predicted drive point,
**not that this point is the exact maximum of a frequency sweep**.

The rational generator reports I(3) ≈ 26.685875 and I(4) ≈ 0.000827837.
These decimal summaries are illustrative; the headline claims are the
rational inequalities above. The exact field witnesses are included in
[ScatteringCertificate](VerifiedPhysics/Experiments/ScatteringCertificate.lean)
and [the certificate input](artifacts/scattering_certificate.json).

The unit source normalizes the second-order equation. In first-order
time-dependent Maxwell equations its magnetic-current amplitude scales as
1/ω, so the comparison is per equal **generalized forcing**, not equal
incident electromagnetic power. The fields are linear-response coefficients;
they can be scaled to arbitrarily weak excitation.

## Error budget

| Contribution | Domain and certified bound | Provenance |
| --- | --- | --- |
| δ_bulk | Zero at a = 0, s ≥ 0, s ≠ 2; polarization error ≤ 3×10⁻⁶ abs(E) for abs(a) ≤ 10⁻⁹ and 3.01 ≤ s ≤ 3.012 | Actual microscopic Hessian and bulk response |
| δ_continuum | Zero algebraic residual for the declared continuum TM solution at (s,k²)=(3,6) | Differential equations and interface conditions |
| δ_finite slab | Frozen allowance abs(s_micro−3) ≤ 0.03; observed s_micro ∈ [3.01,3.012]; frequency error ≤ 0.004 | Independent finite eigenmode certificate and interval-containment theorem |
| δ_momentum | Zero for θ=0, m=1, Λ=2π/√6 | Reciprocal-period identity and explicit mismatch/matching theorems |
| δ_numerical | Zero certificate arithmetic/residual error at a=0, s=3 and 4 | Exact rational primitive-equation and adjoint checks |
| Force linearization | ≤ 40C abs(u)² for abs(u)≤1/2 | Derivative of the nonlinear potential |

The finite-slab allowance includes the combined discrepancy of this particular
box, grid and field basis. It is not a separate convergence bound for each
discretization effect. δ_continuum = 0 does not mean the continuum model is
identical to the microscopic one. There is no amplitude approximation error
borrowed from a continuum solver: the amplitude threshold is a frozen,
falsifiable hypothesis tested by exact microscopic equations.
No statistical uncertainty or sampling assumption enters these claims.

## Dependency isolation and provenance

```text
bulk/effective theory → Prediction/FrozenScatteringPrediction
microscopic model    → Experiments/ScatteringCertificate
                       ↓                   ↓
                       CrossScale/GratingCorrespondence
                                     ↓
                              Final/MainTheorem
```

The prediction closure excludes the experiment, certificates and comparison
modules. The driven certificate closure excludes predictions, effective and
bulk theory, earlier eigenmode certificates, and correspondence modules.
The finite operator is assembled from local curl entries and explicit ionic
Newton equations; the generator never uses a continuum transfer matrix.

[scattering_design.json](artifacts/scattering_design.json) records the
pre-test hypotheses and rejected alternatives.
[Three stage manifests](artifacts/scattering_provenance) hash the baseline,
prediction closure/geometry/interval, and final sources/certificate input.
The candidate generator refuses to run without an intact frozen prediction;
its read-only mode checks deterministic regeneration.
Stage creation refuses to overwrite an existing manifest.
The audit checks all current Lean sources are covered by the final snapshot.

These are locally recorded timestamps and cryptographic identities, **not an
externally timestamped commitment or a Lean proof of historical ordering**.
The execution order in this research session was freeze → solve → check.
The old hash manifest remains unchanged; modified headline/audit files and the
README have their old versions preserved, while new hashes cover current files.

## What is not proved

- Correspondence to real NaCl or any measured material.
- Quantum electronic structure, electronic polarizability or finite temperature.
- Finite-amplitude nonlinear optical dynamics or nonlinear eigenfrequencies.
- Passive grating efficiency, incident/reflected flux, reflectivity, transmission,
  radiative linewidth, damping, or a complete open-boundary scattering spectrum.
- Arbitrary geometries, arbitrary bias in the new driven test, additional Fourier
  orders, or convergence as the finite box/grid/basis changes.
- Uniqueness of every unmeasured field coordinate is not needed or asserted by
  the response certificate; the measured interface amplitudes are unique.
- External cryptographic attestation of the research chronology.

## Reproduction

Use the pinned Lean 4.34.1 toolchain. From `atomcrystal/`:

```sh
# On a fresh checkout, fetch the pinned dependencies and their build cache:
lake update
lake exe cache get

# Verify frozen hashes and deterministically regenerate/check the candidates:
python3 scripts/scattering_provenance.py verify
python3 scripts/scattering.py --check

# Compile all proofs; independently check the final proof environment:
lake build
lake env leanchecker VerifiedPhysics.Final.MainTheorem
lake build VerifiedPhysics.Final.Audit

# Read-only dependency, trust-escape, baseline and final source-hash audit:
python3 scripts/audit.py

# Optional exact regeneration (must reproduce the committed artifacts):
python3 scripts/scattering.py
python3 scripts/scattering.py --check

# Retained earlier numerical experiments:
python3 scripts/research.py bulk
python3 scripts/maxwell_slab.py --prediction artifacts/maxwell_prediction.json
python3 scripts/maxwell_slab.py --prediction artifacts/maxwell_refined_prediction.json
```

In this workspace the available pinned binaries are in
`/tmp/lean-4.34.1-linux/bin`; prepend that directory to PATH if needed.
Python uses only the standard library for the new experiment.
The independent Lean verifier needs the included source/certificates and pinned
Lean dependencies, not the numerical generator.

There are no project-defined axioms, admitted proofs, or native proof shortcuts.
The actual standard logical dependencies are reported by `#print axioms` in
[Final/Audit](VerifiedPhysics/Final/Audit.lean); they include
`propext`, `Classical.choice`, and `Quot.sound`.
See [the final research report](artifacts/scattering_report.md).
