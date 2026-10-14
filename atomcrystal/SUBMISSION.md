# GitHub submission

The repository root is **physlib-experiments/**. This research artifact lives
under `atomcrystal/`, alongside the separate `latticegas/` project. The GitHub
workflow is at `../.github/workflows/verify.yml`, and repository-wide line-ending
rules are at `../.gitattributes`.

## Included research artifact

Commit the Lean sources, Python generators/audits, README, pinned
`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and **all of artifacts/**.
The files under `artifacts/scattering_provenance/baseline_sources/` are intentional
historical snapshots. The rational certificate JSON, generated Lean certificate,
failed experiments, hash manifests and verification records are essential
research evidence, not disposable build output.

The completed scientific snapshot is unchanged. Submission-only files
(`../.gitignore`, `../.gitattributes`, this guide and `../.github/workflows/verify.yml`)
are outside that frozen snapshot. GitHub commits will identify these packaging
files. Do not regenerate frozen manifests merely to add submission metadata.

## Verification

The root-level GitHub workflow runs on pushes, pull requests and manual dispatch,
with both shell steps and the Lean action configured to use `atomcrystal/`.
It checks source identities and exact certificate regeneration, builds with
the pinned Lean toolchain, runs the independent checker, reports logical
dependencies and checks that verification did not alter frozen files.
It uses the official [Lean action](https://github.com/leanprover/lean-action).
The hosted workflow itself has not been run before publication.

Run the following checks from `atomcrystal/` (`cd atomcrystal` from the repository
root). For the fast source-only checks, no Lean installation or dependencies are needed:

```sh
python3 -B scripts/audit.py
python3 -B scripts/scattering_provenance.py verify
python3 -B scripts/scattering.py --check
```

For the full proof build, install Lean through elan, then run:

```sh
lake exe cache get
lake build
lake env leanchecker VerifiedPhysics.Final.MainTheorem
lake build VerifiedPhysics.Final.Audit
lake env lean VerifiedPhysics/Prediction/FrozenScatteringPrediction.lean
python3 -B scripts/audit.py
```

Lake restores dependencies from the committed manifest. Keep that manifest;
dependency updates are separate research changes. Expect several gigabytes
of downloaded dependencies and generated files under `.lake/`, which is ignored.
The full build and independent checker passed before cleanup; build products
are intentionally absent from the submission directory.

## Submit the repository

The parent directory is already a Git repository. From the repository root:

```sh
git add .
git status --short
git commit -m "Submit verified microscopic-to-surface driven-response research"
```

Create an empty GitHub repository, then use its URL:

```sh
git remote add origin YOUR_GITHUB_REPOSITORY_URL
git push -u origin main
```

No remote repository, commit or publication was created during cleanup.
Line endings are fixed to LF so checkout preserves the frozen source hashes.
