# Five-orbital parity energy

At fixed bare pairing strength, moving an outer shell from three to nine
central level spacings lowers the odd–even ground-energy difference of a
five-orbital reduced BCS grain. The parity energy is
`Δₚ = E₅ − (E₄ + E₆)/2`, where `Eₙ` is the ground energy with `n`
electrons. The bare coupling `g` is one thousandth of the central level
spacing, and the table uses `g` as the energy unit.

| Quantity | Value |
| --- | --- |
| Near spectrum | −3000, −1000, 0, 1000, 3000 |
| Far spectrum | −9000, −1000, 0, 1000, 9000 |
| Bare near-minus-far contrast | 0 |
| Derived prediction window, rounded outwards | [0.00010623598, 0.00011598659] |
| Certified full-Hamiltonian contrast | [0.00011129, 0.00011141] |

The proof bounds each sector by two scalar Schur reductions. Both keep the
couplings to the reference occupation, while the maximum discarded row
degree bounds the effect of hops among discarded occupations. Combining the
sector bounds gives the prediction window. [Lean prediction](Grain/Prediction.lean)

An independent full-matrix solve generates rational lower-bound weights
and upper-bound trial vectors. Lean checks those witnesses against the
occupation Hamiltonian and proves that the resulting contrast lies inside
the prediction window. The bare central-orbital model gives zero contrast
for arbitrary frozen outer energies and a common central offset.
[Headline theorem](Grain/Main.lean) · [Full-solve witnesses](artifacts/certificate.json)

## Verify

From this directory with the pinned Lean toolchain and Python 3:

```sh
lake exe cache get Mathlib/Tactic.lean Mathlib/Basic/Real/Basic.lean
lake build
lake env leanchecker Grain.Prediction Grain.Main
python3 -B scripts/certify.py --check
```

The Python check verifies the frozen design and regenerates the JSON
and Lean witnesses byte for byte. The retained source hash records refer
to paths under `superconductivity/` at commit
`3b02be9a797a6d2bac175b3682d93b2175fd9798`. That revision also contains
the original prediction source snapshots.
[Frozen design](artifacts/design.json) ·
[Original hashes](artifacts/prediction.sha256.json) ·
[EFT revision hashes](artifacts/five_orbital_eft.sha256.json)
