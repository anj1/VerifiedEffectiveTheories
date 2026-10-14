# Grand-canonical exact-equilibrium branch: first finite-volume crossing

## Result and scope

The separate zero-field Ising branch has a conditional, familywise-95% finite-volume result: the exact-equilibrium Binder curves for periodic cubic boxes $L=4$ and $L=6$ cross at some $r\in(5/8,2/3)$. The selected endpoint confidence intervals for $U_4(4,r)-U_4(6,r)$ are

| $r$ | interval for $U_4(4,r)-U_4(6,r)$ |
|---|---:|
| $5/8$ | $[-0.067694499932,-0.008003779624]$ |
| $2/3$ | $[0.037975195493,0.203255692835]$ |

The confidence statement is **$P(\text{all four true endpoint Binder values lie in the reported intervals})\ge0.95$** under independent *ideal* random streams and the published empirical-Bernstein inequality. The experiments use deterministic SplitMix64 streams for replayability, so ideal independence is a modeling premise, not an established property of the files. The sign margins are much larger than the numerical guard, but the Decimal transcendental-error guarantee has not been formalized in Lean. Consequently “certified” here means conditional statistical and numerical certification with the gaps explicitly shown in [provenance.json](../grandcanonical_results/provenance.json), not a completely kernel-checked end-to-end claim.

This is a crossing of **two finite-volume curves**, not a measurement of $T_c$, $\nu$, $\eta$, a divergence, or visible-light opalescence. It is not pooled with the earlier fixed-particle Kawasaki experiment.

The claim's dependency chain is visible here; the full typed graph is machine-readable in [provenance.json](../grandcanonical_results/provenance.json):

```text
assumed Ising model + ideal random-stream law
    -> Lean SW marginal / heat-bath monotonicity / CFTP coupling
    -> numerically checked C++ and recorded fresh CFTP holdout
    -> external empirical-Bernstein bound + Lean Binder propagation
    -> conditional 95% endpoint signs + Lean finite-curve continuity
    -> finite-volume crossing
```

## Model and exact mathematical layer

The assumed finite model has $s_x=2n_x-1\in\{-1,+1\}$, periodic cubic edges, and

\[
  \pi_r(s)=\frac{r^{D(s)}}{\sum_{s'}r^{D(s')}},\qquad 0<r<1,
\]

with one edge per site and positive coordinate direction. For a coordination-six lattice gas, $\mu=-3J$ cancels the Ising field; $q=r^2$. This ensemble permits particle-number fluctuations and its data cannot be combined with the canonical data. The $L=2$ validation lattice has parallel periodic edges; the primary crossing uses $L=4,6$.

[GrandCanonical.lean](../lean/GrandCanonical.lean) proves finiteness, positive weights and normalization, the Edwards–Sokal joint spin marginal, rational heat-bath monotonicity, the exact integer threshold equivalence, all-start coalescence from the two extremal trajectories, and stationary CFTP output *conditional on a stationary reference trajectory driven by the same ideal past stream*. It also proves deterministic Binder interval propagation, a probability-coverage implication from moment coverage, finite-moment continuity, and the endpoint-sign-to-crossing theorem specialized to squared magnetization. [GrandCanonicalAudit.lean](../lean/GrandCanonicalAudit.lean) checks theorem axioms; `lake build GrandCanonical` and the audit pass with only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. There are no `sorry` or added physical axioms in this Lean file.

The compiled module was also rechecked with `lake env leanchecker GrandCanonical` (exit status 0).

The C++ simulator is **not extracted from Lean**. An independent Python replay checks three recorded binary past streams against their reported state hashes and exact magnetization moments. A separate exhaustive $2^8$-state enumeration validates both samplers at $L=2$, including all 2,048 site-conditional probabilities at each of two rational parameters. This is a strong implementation check, but not a formal C++ refinement proof. In particular, the general identity between the six-neighbour heat-bath formula and the conditional distribution of $r^{D(s)}$, and the resulting concrete heat-bath stationarity, are **not yet proved in Lean**. The formal CFTP stationarity theorem makes its stationary-reference premise explicit.

## Autonomous experiment record

The initial SW scout used rational $r=3/5,5/8,2/3,7/10$ and $L=4,6,8,12,16$. It found the $L=4$ minus $L=6$ Binder point difference change from −0.0622 at $5/8$ to +0.1003 at $2/3$; the controller requested the mediant $7/11$, then CFTP at the bracket endpoints. It contains no textbook critical parameter. The machine-readable question, observation, experiment, and decision chain is [experiment_log.json](../grandcanonical_data/experiment_log.json). SW is only a scout because its finite sweep count has no equilibrium certificate.

The first implementation produced apparently stable but wrong results. Arithmetic replica seeds shifted the same SplitMix64 stream by one word from one replica to the next, violating the independence premise. The exact $L=2$ check exposed the discrepancy. All version-1 output remains recoverable in grandcanonical_data/invalid_v1/ and is excluded from version-2 analysis. Hashing each replica identifier fixed this specific overlap; the corrected SW and CFTP estimates agree with exact enumeration within sampling variation. This does not prove pseudorandom independence.

An exploratory 20,000-replica CFTP pilot per point gave the sample-size decision. Those samples are **not pooled** into the fixed-size confidence calculation. The fresh holdout used master seed 31427182, 40,000 replicas per size at $5/8$, and 80,000 per size at $2/3$. All 240,000 holdout replicas coalesced before the predeclared cap of $2^{22}$ single-site updates. The observed maximum horizon was $2^{21}$ at $L=6,r=5/8$. No success-only subsampling was used.

For each independent ideal equilibrium draw, $m^2,m^4\in[0,1]$. The certificate applies [Maurer–Pontil's empirical-Bernstein theorem](https://www.cs.mcgill.ca/~colt2009/papers/012.pdf), Theorem 4, to each moment and its complement, with per-tail $\delta=1/320$ and a union bound over 16 events. The moment intervals are propagated through $U_4=1-\langle m^4\rangle/(3\langle m^2\rangle^2)$ using the Lean-proved ratio bound. Exact integer moment sums feed 100-digit Decimal evaluation; outward 12-digit endpoints receive a $10^{-9}$ numerical guard and agree with an independent binary64 calculation. [binder_crossing_certificate.json](../grandcanonical_results/binder_crossing_certificate.json) records every interval, horizon summary, and artifact hash.

## Mesoscopic and probe diagnostics

The scout's $L=16$ axial $S_{\mathrm{spin}}(k_{\min})$ rose from 1.41 at $r=3/5$ to 12.19 at $r=7/11$, roughly an 8.6-fold change. This is a **heuristic equilibrium diagnostic**, not a certified scattering law. CFTP at $r=7/11$ completed 1,000/1,000 replicas for $L=6$, 300/300 for $L=8$, and 40/40 for $L=12$; at $L=16$, 2 of 5 attempts hit the $2^{25}$-update cap, so the three successful states are **not** used as an unbiased sample. This is a clear tractability boundary. The plotted second-moment $\xi_2/L$ values are descriptive ratios of sampled Fourier moments and are not the fragile old two-mode Ornstein–Zernike fit.

The synthetic probe uses an *external* linear dielectric coefficient $a$ and the weak-scattering approximation. For nonzero lattice wavevector, $\delta n_k=s_k/2$, hence the normalized intensity proxy is $I/(|a|^2 V)=S_{\mathrm{spin}}(k)/4$. The linear amplitude-to-intensity algebra is proved in [LatticeGasScattering.lean](../lean/LatticeGasScattering.lean); electromagnetism, the value of $a$, optical wavelengths, and the weak-scattering regime are not derived from this lattice model. [synthetic_probe.svg](../grandcanonical_results/synthetic_probe.svg) is therefore a synthetic, directly accessible-$k$ diagnostic, **not** a prediction of visible opalescence.

Plots: [SW Binder](../grandcanonical_results/binder.svg), [CFTP Binder](../grandcanonical_results/binder_cftp.svg), [second-moment length ratio](../grandcanonical_results/xi2_over_L.svg), [two directly measured Fourier modes](../grandcanonical_results/two_mode_structure_factor.svg), and [synthetic probe](../grandcanonical_results/synthetic_probe.svg). No exponent or scaling-fit plot is supplied because the available sizes and certified points do not support such a fit.

## Reproduction and remaining work

From the repository root, use `ELAN_HOME=$PWD/.elan .elan/bin/lake build GrandCanonical`, then `ELAN_HOME=$PWD/.elan .elan/bin/lake env lean lean/GrandCanonicalAudit.lean`. Compile `src/grandcanonical.cpp` with `g++ -O3 -std=c++20 -Wall -Wextra -Werror -o grandcanonical src/grandcanonical.cpp`. The exact selected holdout commands were:

```sh
./grandcanonical cftp 4 5 8 40000 31427182 4194304 0 grandcanonical_data/raw/cftp_L4_r5_8_n40000.jsonl
./grandcanonical cftp 6 5 8 40000 31427182 4194304 0 grandcanonical_data/raw/cftp_L6_r5_8_n40000.jsonl
./grandcanonical cftp 4 2 3 80000 31427182 4194304 0 grandcanonical_data/raw/cftp_L4_r2_3_n80000.jsonl
./grandcanonical cftp 6 2 3 80000 31427182 4194304 0 grandcanonical_data/raw/cftp_L6_r2_3_n80000.jsonl
cd scripts
python3 grandcanonical_validate.py
python3 grandcanonical_analysis.py
python3 grandcanonical_certify.py
python3 grandcanonical_decide.py
cd ..
```

Re-running those CFTP commands overwrites the named output files; copy the raw directory first if the existing artifacts must be retained byte-for-byte. Remaining work is to formalize the concrete heat-bath stationarity step, empirical-Bernstein theorem, and C++ refinement; use a genuinely independent random-bit source with recorded streams for stronger exact-distribution provenance; add another size-pair crossing and quantify crossing drift; then attempt $\nu$ and $\eta$. Neither universality nor visible-light scattering has been tested.
