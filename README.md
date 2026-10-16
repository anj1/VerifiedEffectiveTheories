# Physics research experiments

AI has recently had some [amazing](https://openai.com/index/navier-stokes-solution/) [results](https://github.com/openai/math) in mathematics. This opens up the question of whether we might be able to use AI in physics to achieve breakthroughs of similar magnitudes. There are currently many problems in physics that have remained unsolved despite decades of study, in for instance materials science and plasma physics.

At first glance it might look like math and physics are very different; ai uses formal verification tools (like Lean) that can run entirely inside a computer. Usual physics research involves setting up real-world experiments but they're expensive and time-consuming and take a long time to do and interpret.
You could in principle avoid experiments and derive everything from first principles (quantum mechanics, quantum field theory) but for any macroscopic system it's basically infeasible.

This repo explores an alternative way: Building up effective theories instead. The procedure is: start from a low level of theory, construct systems of manageable size, derive laws, and then renormalize to a larger scale (abstracting away details) and see how the laws translate over. The key "trick" is you do the whole thing with Lean, so you know exactly what assumptions you're making at each step and can prove that your macroscopic law actually does work in the regime you're interested in.

So then theoretical physics research basically becomes math research: you can state laws (conjectures), try to prove them, or find counterexamples (novel phenomena, anomalous observations).

An important caveat is that things are only proven relative to the core postulates (axioms). You can in principle go quite deep, deriving from quantum field theory, with the downside being a more complex problem to solve. But more importantly, most interesting physics happens at the level of the effective theory.

The following is an AI-generated description of the results of these experiments so far.

## Experiments

This repository contains two separate projects with different verification
and data-retention scopes.

## Atomcrystal: microscopic ions to surface-field enhancement

![From microscopic polar dimers to a momentum-matched, Lean-verified surface response](atomcrystal/assets/verified_surface_physics.svg)

[`atomcrystal/`](atomcrystal/README.md) completes a finite-model research loop:

```text
nonlinear ionic potential → bulk dielectric law → continuum surface mode
→ momentum-matched experiment → independent microscopic driven calculation
→ certified observable and discrepancy bounds
```

The model is a finite polar-dimer crystal with 64 ions and explicit Maxwell
fields. The effective theory identifies a parallel-momentum mismatch and
selects a periodic source. A prediction frozen before the driven calculation
is then validated by exact rational certificates checked in Lean.

The [headline theorem](atomcrystal/VerifiedPhysics/Final/MainTheorem.lean),
`verified_automated_surface_physics`, combines a surface eigenfrequency bound
of `0 < ω_micro − √3 ≤ 0.004` with a driven interface magnetic-intensity
contrast of at least four and at least 60% near-interface magnetic localization.
Earlier failed predictions remain part of the research record.

This is linear response in a specified synthetic material, using an ideal
prescribed periodic source. It does not prove real NaCl behavior, passive-grating
efficiency, or open-boundary reflectivity. Proof sources, certificates, frozen
predictions, and provenance records are included.

See the [project README](atomcrystal/README.md) for assumptions and error budgets,
the [final report](atomcrystal/artifacts/scattering_report.md) for the research
outcome, and the [submission guide](atomcrystal/SUBMISSION.md) for repository
and verification details.

## Lattice gas: finite-volume fluctuations and scattering

[`latticegas/`](latticegas/README.md) explores local lattice interactions,
density fluctuations, finite-volume Binder crossings, and synthetic scattering
enhancement. It includes simulation code, conditional Lean theorems, and
historical reports covering both successful finite-volume comparisons and
a failed exploratory exponent-compatibility test.

This project is a lightweight source-only archive: its original generated
samples, random streams, and numerical certificates were removed. The Lean
theorems check conditional mathematical implications; the historical empirical
premises cannot be independently re-audited from this checkout alone.
New simulations do not restore the deleted historical samples.

See the [project README](latticegas/README.md) for dependency setup and rerun
instructions, and the [report index](latticegas/reports/README.md) for the
findings and their limitations.

## Verify atomcrystal

The source and provenance checks require only Python 3. From the repository root:

```sh
python3 -B atomcrystal/scripts/audit.py
python3 -B atomcrystal/scripts/scattering_provenance.py verify
python3 -B atomcrystal/scripts/scattering.py --check
```

For the full proof build, install Lean through elan, then use the pinned
toolchain and dependency manifest:

```sh
cd atomcrystal
lake exe cache get
lake build
lake env leanchecker VerifiedPhysics.Final.MainTheorem
lake build VerifiedPhysics.Final.Audit
```

The [GitHub workflow](.github/workflows/verify.yml) runs atomcrystal's build,
independent proof checking, certificate regeneration, and provenance audits.
It does not currently verify the lattice-gas project.

Downloaded dependencies and build products are excluded from version control
and are restored when building. Atomcrystal's `artifacts/` directory contains
required scientific evidence and must be retained. Repository-wide LF
line-ending rules preserve its frozen source hashes across checkouts.
