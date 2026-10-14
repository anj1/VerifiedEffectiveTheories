# Research banner

![Microscopic polar dimers, momentum-matched excitation and the certified surface response](verified_surface_physics.svg)

**Figure. From microscopic ions to a verified surface response.** A stable
Coulomb-plus-short-range polar-dimer model yields an axial Hessian and a bulk
dielectric law. The continuum surface excitation at squared frequency
`s = ω² = 3` requires parallel momentum `√6`, outside the propagating vacuum
range at that frequency. Normal incidence and a prescribed periodic source
with period `2π/√6` supply the missing momentum. An independently specified
finite ionic–Maxwell calculation certifies the frozen interface-intensity
contrast, nonzero ionic response, and near-interface magnetic localization.
The frequency enclosure on the right is the preserved finite eigenmode result;
it is distinct from the new driven comparison at `s = 3` and `s = 4`.

The displayed depth profile uses the **exact rational magnetic amplitudes** of
the drive solution in
[`scattering_certificate.json`](../artifacts/scattering_certificate.json),
squared and normalized by their maximum. Points lie at the 32 magnetic-cell
centers; lines between them are graphical interpolation. The background field
uses the same depth samples multiplied by a schematic transverse `cos²(Gx)`
profile. The highlighted strip is `|z| ≤ 1`, inside conducting boundaries at
`z = ±2`. The arrangement and number of drawn dimers are illustrative, not
an atom-by-atom rendering of the 64-ion geometry. The spring symbol illustrates
the retained linearized coordinate; the assumed microscopic interaction is
the nonlinear potential, and `U″(0)` denotes its axial Hessian.

All units are dimensionless. The intensity comparison is per equal generalized
source forcing, not equal incident power. The coupler is an ideal impressed
source, not a passive corrugation. No reflectivity, passive-grating efficiency,
real-material correspondence, or finite-amplitude nonlinear response is claimed.

## Reproduce or export

The SVG is self-contained, editable vector artwork with live text, an accessible
title and description, and no external image or font dependencies. Its canvas is
1800 × 900, suitable for a wide article figure. DejaVu Sans is preferred, with
system font fallbacks.

From `atomcrystal/`, using only the Python standard library:

```sh
python3 -B scripts/render_banner.py
python3 -B scripts/render_banner.py --check
```

For a publication PDF or a higher-resolution PNG, if Inkscape is installed:

```sh
inkscape assets/verified_surface_physics.svg --export-type=pdf --export-text-to-path --export-filename=/tmp/atomcrystal-banner.pdf
inkscape assets/verified_surface_physics.svg --export-width=3600 --export-type=png --export-filename=/tmp/atomcrystal-banner.png
```

The illustration and renderer are presentation additions made after the frozen
research result. They do not modify its sources, prediction, certificates or
hash manifests. The mathematical claims are those of
[`verified_automated_surface_physics`](../VerifiedPhysics/Final/MainTheorem.lean).
