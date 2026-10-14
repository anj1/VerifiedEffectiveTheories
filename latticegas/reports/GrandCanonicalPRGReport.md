# Phenomenological-renormalization branch: certified second crossing

The subsequent Binder-refined quotient experiment and its negative scattering-dimension compatibility result are documented in [GrandCanonicalPRGStage5Report.md](GrandCanonicalPRGStage5Report.md). This earlier report remains the record of the first certified crossing stage.

## Outcome

The microscopic heat-bath gap is closed in Lean. For the concrete periodic cubic lattice with (L\ge2), the six-neighbour probability used by CFTP is the conditional distribution of the finite Gibbs law (\pi_r(s)\propto r^{D(s)}). The corresponding one-site kernel is nonnegative, stochastic, detailed-balanced, and stationary. Lean also proves

\[
r\frac{d}{dr}\mathbb E_r[f]=\operatorname{Cov}_r(f,D)
\]

and the resulting Binder-slope identity. Thus no finite differences or histogram reweighting are used for slopes. `lake build GrandCanonicalPRG`, `leanchecker GrandCanonicalPRG`, and the `GrandCanonicalAudit.lean` axiom audit passed. The audit lists only `propext`, `Classical.choice`, and `Quot.sound`.

A fresh SW scout requested an (8\to12) CFTP test. The first 1,000-draw endpoint batches suggested a crossing but separate-moment confidence boxes failed. A covariance-aware certificate and two independent holdout stages now establish, **conditional on ideal iid equilibrium draws and the external concentration theorem**, that the exact finite-volume Binder curves for (L=8) and (L=12) cross at some (r\in(7/11,20/31)), with familywise confidence at least 95%. All 70,000 CFTP draws used in the final sign test coalesced; another 10,000 high-side design draws also coalesced but were not pooled into that test. No burn-time assumption was used. Lean proves the deterministic passage from endpoint ratio signs to this finite-volume crossing. This is a second scale-factor (3/2) crossing, following the earlier (4\to6) result. It is **not** a certification of (T_c), (\nu), (\eta), or infinite-volume universality.

## Model and trust boundary

- **Assumed microscopic model:** finite zero-field, grand-canonical Ising law on the cubic torus, (\pi_r(s)\propto r^{D(s)}), rational (0<r<1). This branch is separate from the old canonical Kawasaki data.
- **Formally proved:** local disagreement identity, Gibbs conditional, heat-bath detailed balance/stationarity, monotone all-start coalescence certificate, covariance derivative, Binder derivative, centered Binder sign/coverage propagation, and a finite-volume crossing theorem from four ratio signs. The prior CFTP theorem remains conditional on a stationary reference trajectory driven by an ideal past stream; construction of that two-sided process is not yet formalized here.
- **Executable check:** exact integer heat-bath thresholds and selected independent Python replays match recorded magnetization, (D), plane sums, and state hashes. This is not a universal compiler-correctness theorem for C++.
- **Statistical assumption:** ideal independent unbiased random words would make separate CFTP outputs iid equilibrium draws. SplitMix64 is a deterministic replay device, not a proof of this assumption. Distinct seeds/domain separation prevent accidental stream reuse but do not imply independence.
- **Numerical boundary:** moment sums are exact integers. Lowest Fourier powers are reconstructed as (P+Q\sqrt2) or (P+Q\sqrt3) from integer plane sums, with a 30-digit rational enclosure made by integer square root. The Fourier tables have not yet been proved in Lean; floating FFT values are diagnostics only. The earlier separate-moment analysis used a guarded Decimal logarithm, but the successful crossing sign test uses only rational arithmetic.

The original separate-moment boxes use [Maurer–Pontil's empirical-Bernstein theorem](https://www.cs.mcgill.ca/~colt2009/papers/012.pdf) and Lean-proved Binder interval propagation. The successful centered certificate uses the same external theorem on (m²) and one covariance-aware observable at each of four cells. Its logarithm is bounded by the exactly checked inequality (\log 320<6); square-root bounds and all sign calculations use rational integers, not floating point. The eight two-sided intervals each have failure allowance (1/160), summing to (0.05). The external concentration theorem itself is not yet formalized in Lean. [The quotients method](https://www.nature.com/articles/s41586-024-07647-y) motivates comparing observables at a crossing, but does not authorize calling a nearby sampled parameter a crossing.

## Adaptive experiment sequence

The [structured experiment log](../grandcanonical_results/prg_experiment_log.json) records each question, proposed experiment, observation, and decision. The key course corrections were failures: at (L=12,r=5/8), all five CFTP feasibility streams were censored at (2^{25}) updates, and the first separate-moment confidence boxes failed to certify the crossing. No censored subset was analysed. A fresh nearby scout and feasibility test made (7/11) a tractable negative-side endpoint. After the first centered 5,000-draw stage certified only the low-side signs, its high-side data became *design-only*; a fresh 30,000-draw stage at (20/31) used a pilot-frozen threshold. The known critical coupling supplied for debugging was not inserted into any scout or selection rule.

Every result has model version, (L), rational (r), replica, seed, initial condition, coalescence horizon, (D), moments, plane sums, and state hash in [raw JSONL data](../grandcanonical_data/prg_raw). The primary new implementation is [grandcanonical.cpp](../src/grandcanonical.cpp), version `grandcanonical-v4-prg`; earlier datasets were not merged or rewritten. Selected first streams from every final holdout cell were independently replayed in Python and matched their state hashes, (D), magnetization, and plane sums. This is a diagnostic, not a universal C++ refinement proof.

## Exact-sample crossing certificate

Let (a=E[m²]), (b=E[m⁴]), (R=b/a²), and (F_c=b-ca²). Since (U_4=1-R/3), opposite signs of (F_c) at the two sizes order the two Binder curves. A pilot-frozen center (a_0) gives the exact identity

\[
F_c=E[m^4-2ca_0m^2]+ca_0^2-c(a-a_0)^2.
\]

Bounding the *single* centered random observable retains the covariance of (m²) and (m⁴). A separate bound on (a) controls the final square. [Lean's centered-sign and crossing theorems](../lean/GrandCanonicalPRG.lean) verify the deterministic propagation. The following intervals come from [exact-rational certificate output](../grandcanonical_results/prg_covcert.json) for the low side and [independent stage-two output](../grandcanonical_results/prg_covcert2.json) for the high side. They jointly carry the conditional familywise 95% guarantee; the point estimates alone do not.

| (r) | (L) | fresh (n) | threshold (c) | point (U_4) | confidence interval for (F_c) | certified sign |
|---|---:|---:|---:|---:|---:|---|
| (7/11) | 8 | 5,000 | 1.27 | 0.55056 | [0.00132942, 0.00719414] | positive |
| (7/11) | 12 | 5,000 | 1.27 | 0.59670 | [-0.00522207, -0.00035686] | negative |
| (20/31) | 8 | 30,000 | 1.75 | 0.43097 | [-0.00152488, -0.00014574] | negative |
| (20/31) | 12 | 30,000 | 1.75 | 0.38541 | [0.00004945, 0.00102329] | positive |

Thus (U_4(8,7/11)<U_4(12,7/11)) and (U_4(8,20/31)>U_4(12,20/31)) hold with joint confidence at least 95% **under ideal independent exact-equilibrium samples**. Finite-volume Gibbs expectations are continuous in (r), and Lean proves that these opposite endpoint signs imply at least one crossing in (7/11,20/31). The interval is a crossing bracket, **not** an infinite-volume critical parameter interval. The two 5,000-draw high-side cells from stage one did not certify their signs and were used only to choose the fresh stage-two threshold; none of their observations were pooled into the successful confidence calculation.

The earlier 1,000-draw separate-moment boxes were [-0.53943, 0.49417] at (7/11) and [-2.20270, 12.63776] at (13/20); both contained zero despite suggestive point estimates. This negative result motivated the centered observable, not a change to the physics. The previous (4\to6) certificate remains untouched and separate.

At (r=16/25), another 6,000 fresh coalesced replicas were gathered: 2,000 each at (L=4,6) and 1,000 each at (L=8,12). The Binder differences at that common parameter are +0.01643 for (4\to6) and -0.02172 for (8\to12), indicating crossing drift. Neither sign at that *particular parameter* has the finite-sample certificate used above. The certified (8\to12) crossing may lie elsewhere within its bracket.

## Provisional scale transformation and scattering observable

At a **genuine pair crossing**, the quotients would be

\[
Q_U=\frac{|U_4'(sL)|}{|U_4'(L)|},\quad
\nu_{\rm eff}=\frac{\log s}{\log Q_U},\qquad
Q_S=\frac{S_{sL}(k_{\min})}{S_L(k_{\min})},\quad
\eta_{\rm eff}=2-\frac{\log Q_S}{\log s}.
\]

The table evaluates the same formulas at (r=16/25), where (s=3/2), **without claiming the parameter is either pair's crossing**. Existence of a crossing somewhere in (7/11,20/31) does not make (16/25) its location. The derivative (U_4'=dU_4/d\log r) comes from the exact covariance identity; (S) is the spin structure factor averaged over the three lowest axis modes. The density version differs by a fixed normalization, so its size ratio is the same.

| pair | (Q_U) | (\nu) proxy | (Q_S) | (\eta) proxy |
|---|---:|---:|---:|---:|
| (4\to6) | 2.432 | 0.456 | 2.061 | 0.217 |
| (8\to12) | 1.774 | 0.707 | 2.055 | 0.224 |

The exploratory bootstrap 95% intervals for the (\nu) proxies are [0.391,0.538] and [0.495,1.187]; for (\eta), [0.111,0.334] and [0.071,0.381]. The thermal quotient drifts markedly, while the lowest-mode scattering quotient is similar across the two scale transformations. This is evidence worth following up, not an asymptotic law. No (T_c), (\nu), (\eta), or (\omega) fit is made.

With an *assumed* linear dielectric coupling and weak scattering, intensity is proportional to the density structure factor. Thus (Q_S\simeq2.05) is a conditional prediction for the ratio of scattering strengths at the two different accessible wavevectors (2\pi/L), not a fixed-wavelength or visible-light prediction. The lattice gas contains no electromagnetism.

At the high-side endpoint (20/31), the 30,000-draw exploratory point estimates are (S_{12}(k_{\min})/S_8(k_{\min})\simeq 2.215) and (|U'_{12}|/|U'_8|\simeq 1.896). These have not yet been given finite-sample quotient intervals and are not evaluated at the certified crossing. They therefore remain diagnostics, not (\nu_{\rm eff}) or (\eta_{\rm eff}).

Plots: [Binder curves](../grandcanonical_results/prg_binder_curves.svg), [Binder differences](../grandcanonical_results/prg_binder_difference.svg), [centered sign bounds](../grandcanonical_results/prg_covariance_signs.svg), [log scaling](../grandcanonical_results/prg_log_scaling.svg), and [quotient drift](../grandcanonical_results/prg_quotient_drift.svg). Plotting uses ordinary floating point and is not part of the trusted inference.

## Next decision

The immediate milestone—an independently certified second finite-volume crossing at scale factor (3/2)—is achieved. The next experiment should narrow the crossing bracket with SW scouting followed by fresh CFTP signs, then gather exact samples at a predeclared approximation to each pair's crossing. Only at those pair-specific crossing parameters should Binder-slope and lowest-mode scattering quotients be promoted from proxies to uncertainty-bounded (\nu_{\rm eff}) and (\eta_{\rm eff}). The crossing drift itself is now a target observable for finite-size corrections. Do not fit (T_c), (\nu), (\eta), and (\omega) jointly from these two small-size pairs. CFTP cost at (L=12) remains significant; if a larger pair becomes infeasible, investigate perfect random-cluster sampling rather than returning to finite-burn local dynamics.

The [machine-readable provenance graph](../grandcanonical_results/prg_provenance.json) marks every node as assumed, proved, numerically checked, statistically inferred, or heuristic. The [crossing certificates](../grandcanonical_results/prg_covcert2.json), [first-stage data](../grandcanonical_results/prg_covcert.json), and [earlier quotient analysis](../grandcanonical_results/prg_analysis.json) include raw/code SHA-256 hashes, rational uncertainty bounds, coalescence counts, algebraic Fourier enclosures, and the provisional quotient calculations.

## Reproduce and audit

```bash
ELAN_HOME=$PWD/.elan PATH=$PWD/.elan/bin:$PATH lake build GrandCanonicalPRG
ELAN_HOME=$PWD/.elan PATH=$PWD/.elan/bin:$PATH lake env leanchecker GrandCanonicalPRG
ELAN_HOME=$PWD/.elan PATH=$PWD/.elan/bin:$PATH lake env lean lean/GrandCanonicalAudit.lean
python3 scripts/prg_validate.py
python3 scripts/prg_analyze.py
python3 scripts/prg_covcert.py
python3 scripts/prg_covcert2.py
python3 scripts/prg_plots.py
```

`scripts/prg_scout.py`, `scripts/prg_refine.py`, and `scripts/prg_refine2.py` reproduce the adaptive scouting artifacts; they must not be pooled into the CFTP confidence calculation. The v4 executable is built with `g++ -O3 -std=c++20 -Wall -Wextra -Werror src/grandcanonical.cpp -o scripts/build/grandcanonical_prg_v4`.
