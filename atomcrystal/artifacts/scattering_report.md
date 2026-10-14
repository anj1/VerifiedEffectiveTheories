# Final research report: the withheld driven experiment

## Scientific outcome

The finite driven-response version of the research loop is closed by
`VerifiedPhysics.verified_automated_surface_physics`. The material remains the
specified synthetic polar-dimer crystal. The new experiment is a momentum-
matched ideal impressed source, with explicit microscopic ions and Maxwell
fields. It is not a passive grating or an open-boundary reflection calculation.

The effective TM solution at squared frequency 3 and squared momentum 6
motivated the experiment. For every incidence angle, vacuum parallel momentum
is below sqrt(6) throughout [2.97,3.03]. The selected normal-incidence,
first-order source period 2*pi/sqrt(6) supplies that momentum exactly.

The first lower-level driven solve occurred only after freezing the source
recipe and these quantitative hypotheses:

- Drive at squared frequency 3; control at squared frequency 4.
- Unit generalized magnetic source in vacuum cell 15; all other rows zero.
- Interface magnetic intensity at the drive is at least 1.
- Drive intensity is at least four times control intensity.

Both frozen hypotheses passed. Exact rational witnesses satisfy every primitive
field and ionic equation. Exact adjoint witnesses show that both measured
interface magnetic amplitudes are the same for every solution at each tested
frequency. The formally proved bounds are I(3) >= 1, I(4) <= 1/4,
I(3) >= 4 I(4), and I(3)-I(4) >= 3/4. At least 60% of magnetic intensity
lies within distance one of the interface, and the ionic response is nonzero.

Illustrative numerical evaluations of the exact witnesses are 26.6858747445
and 0.000827836751, with drive localization about 97.386%. These decimals
are not substituted for the rational inequalities in the scientific claim.

The existing eigenmode remains in [3.01,3.012], a squared-frequency enclosure
of width 1/500, contained in the frozen [2.97,3.03] window. Its frequency
differs strictly positively from sqrt(3) by at most 1/250. The driven test
is new; the pre-existing eigenfrequency is not represented as newly withheld.
No maximum of a driven frequency sweep is asserted.

## Provenance and falsifiability

The baseline was built, independently checked and archived first. Prediction
modules were then compiled and hashed, along with the geometry, frequencies,
interval and thresholds in scattering_design.json. Only then was scattering.py
implemented and first run. No threshold, frequency or prediction interval was
changed after that run. Later certificate improvements prove uniqueness of
the observable and connect it to physical curl and ionic equations.

The prediction's transitive imports contain no withheld experiment. Conversely,
the driven certificate contains no imports of effective/bulk predictions or the
old eigenmode certificate. Independent assembly uses the local finite curl and
ionic Newton equations. Python produces rational candidates; Lean checks all
claimed identities and inequalities without trusting the solver.

The archived coarse failures and old refined successes remain. The audit also
checks that the previous headline theorem bodies are unchanged. A local
SHA-256 hash chain identifies the baseline, frozen prediction and final result.
It is not an externally attested chronology or a cryptographic theorem in Lean.

## Scope and uncertainty

Scattering is certified at zero microscopic bias; the preserved bulk/eigenmode
theorem separately covers absolute bias at most 10^-9. Exact zero-bias bulk and
continuum algebra have zero residual, ideal momentum error is zero, and rational
certificate error is zero. The finite-model squared-frequency allowance is
0.03, with actual certified enclosure [3.01,3.012]. These quantities are not
summed across unlike units. The interval containment is proved in Lean.

The normalized observable compares equal forcing in CE-sH=J. In first-order
Maxwell time equations, the impressed magnetic current scales as J/omega.
Thus this is not an equal-incident-power reflectivity measurement. A prescribed
source supplies the momentum; passive conversion efficiency and additional
diffraction channels are not inferred from this model.

The microscopic nonlinear force remainder is bounded by 40*C*abs(u)^2 for
abs(u)<=1/2. The optical result is infinitesimal linear response, not a theorem
about finite-amplitude nonlinear trajectories. Real-material correspondence,
quantum electronic structure, temperature, open-boundary radiation, damping,
passive scattering efficiency and general grid convergence remain unproved.

## Verification and reproduction

The full Lean build, independent leanchecker verification of the final module,
and deterministic certificate regeneration passed. Final/Audit reports exactly
`propext`, `Classical.choice`, `Quot.sound` for the headline theorem, physical
driven equations and uniqueness certificate. No project-defined logical
assumptions, admitted proofs or native numerical proof shortcuts are used.

The recorded command output is in scattering_verification.json. From the project
root, reproduce with:

```sh
lake build
lake env leanchecker VerifiedPhysics.Final.MainTheorem
lake build VerifiedPhysics.Final.Audit
lake env lean VerifiedPhysics/Prediction/FrozenScatteringPrediction.lean
python3 scripts/scattering.py --check
python3 scripts/scattering_provenance.py verify
python3 scripts/audit.py
```

Use `python3 scripts/scattering.py` to regenerate the candidate JSON and Lean
certificate exactly. Existing frozen stage files must be kept; stage creation
refuses to overwrite them. The README describes dependencies, source assumptions,
the uncertainty budget and the preserved earlier experiments.
