# Finite-volume two-scale pseudocriticality and long-wavelength amplification

![Schematic banner of the two-scale finite-volume theorem and its conditional coverage](../assets/two_scale_pseudocriticality.svg)

## Final result

The final kernel-checked statement is
[`GrandCanonical.two_scale_pseudocriticality_and_amplification`](../lean/GrandCanonicalFinal.lean).
It concerns the finite periodic cubic zero-field Ising family with
\(\pi_r(s)=r^{D(s)}/\sum_t r^{D(t)}\), \(0<r<1\). Its population Binder
curve uses \(m=V^{-1}\sum_xs_x\), and its population spin structure factor
averages the three axial modes at each box's own \(k_{\min}=2\pi/L\).

**Conditional on the eight certified population Binder endpoint signs and
eight population structure-factor enclosures explicitly listed as theorem
hypotheses**, Lean proves that there are exact finite-volume crossings

\[
U_4(r_{46})=U_6(r_{46}),\quad r_{46}\in(12/19,11/17),
\qquad
U_8(r_{812})=U_{12}(r_{812}),\quad r_{812}\in(7/11,20/31).
\]

It also proves the larger-pair bracket is strictly inside the smaller-pair
bracket and \(\lvert r_{46}-r_{812}\rvert<8/589\). At independently frozen
*near-crossing sampling parameters* \(16/25\) and \(34/53\), respectively,
the theorem concludes

\[
1.872<\frac{S_6(16/25)}{S_4(16/25)}<2.204,
\qquad
1.559<\frac{S_{12}(34/53)}{S_8(34/53)}<3.015.
\]

The population \(S_L(r)\) here is the spin-mode power at each size's own
lowest axial wavevector. The second upper limit is **3.015, not 3.014**:
the exact-rational certificate's upper endpoint is approximately
3.014187995, so 3.014 would be an invalid inward rounding. Both quotient
lower limits exceed one. These are finite-volume, size-dependent-wavevector
amplifications; the theorem asserts neither an infinite-volume critical
point nor a fixed-wavelength optical effect.

## Coverage and the unsuccessful global recertification

The [small-pair Binder certificate](../grandcanonical_results/prg_stage4_repair_certificate.json)
and [large-pair certificates](../grandcanonical_results/prg_covcert.json)
([upper endpoint](../grandcanonical_results/prg_covcert2.json)) each cover their
four required signs jointly with at least 95% probability. The
[four scattering-mean certificates](../grandcanonical_results/prg_stage5_analysis.json)
jointly cover their corresponding population values with at least 95%.
These guarantees are conditional on **independent exact-equilibrium draws
from ideal iid random instructions** and the *external*, not Lean-proved,
Maurer–Pontil empirical-Bernstein inequality. Lean's
[`three_familywise_cover`](../lean/GrandCanonicalFinal.lean) proves that three such
95%-coverage events have simultaneous coverage at least **85%**, without an
independence assumption between the three event families. The deterministic
final theorem turns simultaneous premise coverage into the stated physical
conclusions. SplitMix64 only provides replayability; it is not an iid proof.

I recomputed **only the existing raw samples** with a uniform global
allocation of 20 two-sided empirical-Bernstein events at \(\delta=1/400\)
each, totaling 5% familywise error. This used exact rational arithmetic,
\(\log(800)<7\) checked by a rational Taylor partial sum, and previous raw
hashes verified against their certificates. The
[machine-readable calculation](../grandcanonical_results/prg_final_global_cert.json)
retains seven of eight Binder signs; the \(L=12,r=20/31\) sign becomes
unresolved, with centered-\(F\) interval approximately
\([-2.1045\cdot10^{-5},,1.0924\cdot10^{-3}]\).
Both widened scattering quotient lower limits still exceed one
(about 1.851 and 1.474). Consequently **no 95% simultaneous final claim is
made**. This post-hoc allocation is a sensitivity calculation, not a new
predeclared confirmation. No additional simulation was run.

## Provenance and limits

The microscopic Gibbs law is an assumed physical model. Its finite heat-bath
conditional, detailed balance, stationarity, and monotone CFTP coalescence
logic are in [GrandCanonicalPRG.lean](../lean/GrandCanonicalPRG.lean) and
[GrandCanonical.lean](../lean/GrandCanonical.lean). The exact-sampling conclusion
still assumes an ideal two-sided stationary reference construction and iid
random instructions. The C++ sampler uses exact integer update thresholds;
selected streams were independently replayed, but no universal C++/Lean
refinement proof exists. The Fourier analyzer uses algebraic numbers with
outward rational enclosures; its finite trigonometric lookup table is not
yet proved equivalent in Lean to the complex-exponential definition in the
final theorem. These are explicit provenance boundaries, not hidden theorems.

The earlier attempt to extract compatible finite-size scattering dimensions
from the two pairs **failed its predeclared exploratory comparison** after a
Binder-only correction. Details and the negative result remain in the
[stage-five report](GrandCanonicalPRGStage5Report.md). Neither thermal nor
correlation exponents, \(T_c\), or “RG fixed point” form part of this final
result. A weak-scattering dielectric probe would inherit the measured
structure-factor ratio only under an *external* probe coupling and the
weak-scattering approximation. Because \(k_{\min}\) changes with \(L\), this
does not establish visible-light critical opalescence.

The [final dependency graph](../grandcanonical_results/prg_final_provenance.json)
separates assumptions, formal proofs, raw data, numerical checks, external
statistics, conditional inference, and the exploratory failure. The
[source-relocation manifest](../grandcanonical_results/source_relocation.json)
maps historical artifact paths to the tidied source layout and checks that
all relocated source bytes retain their recorded SHA-256 hashes. The
[structured experiment log](../grandcanonical_results/prg_experiment_log.json)
and [raw CFTP records](../grandcanonical_data/prg_raw) remain unchanged.

## Verification

Run `ELAN_HOME=$PWD/.elan .elan/bin/lake build GrandCanonicalFinal`,
`ELAN_HOME=$PWD/.elan .elan/bin/lake env leanchecker GrandCanonicalFinal`,
and `ELAN_HOME=$PWD/.elan .elan/bin/lake env lean lean/GrandCanonicalAudit.lean`.
The last command prints only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms for both final theorems. Recompute the existing-data
sensitivity calculation with `python scripts/prg_final_global_cert.py`; it verifies
the source hashes before writing its certificate. No `sorry` or custom axiom
occurs in the final Lean module.
