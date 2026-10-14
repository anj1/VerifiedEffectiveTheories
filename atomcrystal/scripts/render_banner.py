#!/usr/bin/env python3
"""Render the research banner as a self-contained, reproducible SVG.

The depth profile uses exact rational magnetic amplitudes from the included
certificate. Float conversion is for drawing only, never for proof checking.
The ionic arrangement and transverse span are schematic. No external fonts,
images, plotting libraries, or network access are needed.
"""
import argparse
import json
import math
from fractions import Fraction
from html import escape
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "assets/verified_surface_physics.svg"


def render():
    data = json.loads((ROOT / "artifacts/scattering_certificate.json").read_text())
    fields = data["results"]["resonant"]["fields"]
    # Top to bottom: z=+2 vacuum wall, interface, z=-2 material wall.
    h = [Fraction(x) for x in fields["vacuumH"]]
    h += [Fraction(x) for x in reversed(fields["materialH"])]
    intensities = [x*x for x in h]
    maximum = max(intensities)
    profile = [float(x/maximum) for x in intensities]
    svg = ['''<svg xmlns="http://www.w3.org/2000/svg" width="1800" height="900"
  viewBox="0 0 1800 900" role="img" aria-labelledby="title description">
<title id="title">From microscopic ions to a verified surface response</title>
<desc id="description">Research banner for atomcrystal. A stable 64-ion polar-dimer
model yields a bulk dielectric law and a surface-mode prediction. Direct vacuum
incidence cannot supply the required parallel momentum. An ideal periodic source
with period two pi over square root six supplies that momentum. An independent
finite ionic-Maxwell driven calculation certifies at least fourfold interface
magnetic-intensity contrast, at least sixty percent near-interface magnetic
localization, and the preserved eigenfrequency discrepancy bound of 0.004.
The central normalized magnetic-intensity depth profile is drawn from the exact
rational drive certificate at squared frequency three. Ion positions are schematic.
The comparison uses equal generalized source forcing, not equal incident power;
no passive-grating efficiency or reflectivity is claimed.</desc>
<defs>
  <linearGradient id="paper" x2="0" y2="1">
    <stop stop-color="#fbfcfd"/><stop offset="1" stop-color="#edf3f5"/>
  </linearGradient>
  <linearGradient id="material" x2="0" y2="1">
    <stop stop-color="#e4f2f1"/><stop offset="1" stop-color="#d2e4e7"/>
  </linearGradient>
  <marker id="arrow" markerWidth="8" markerHeight="8" refX="6" refY="3"
    orient="auto" markerUnits="strokeWidth"><path d="M0 0L6 3L0 6Z" fill="#476779"/></marker>
  <marker id="tealArrow" markerWidth="8" markerHeight="8" refX="6" refY="3"
    orient="auto" markerUnits="strokeWidth"><path d="M0 0L6 3L0 6Z" fill="#007d83"/></marker>
  <clipPath id="fieldClip"><rect x="468" y="318" width="614" height="300" rx="4"/></clipPath>
  <style>
    text { font-family: "DejaVu Sans", Arial, sans-serif; fill: #162f43; }
    .eyebrow { font-size: 13px; font-weight: 700; letter-spacing: 2px; fill: #5b7180; }
    .label { font-size: 15px; fill: #4f6676; }
    .small { font-size: 12px; fill: #58707d; }
    .formula { font-family: "DejaVu Sans", Arial, sans-serif; font-size: 23px; }
    .card { fill: #fff; stroke: #d9e4e9; stroke-width: 1.2; }
    .rule { stroke: #dbe5e9; stroke-width: 1; }
  </style>
</defs>
<rect width="1800" height="900" fill="url(#paper)"/>
<path d="M48 50H86" stroke="#00858a" stroke-width="4"/>
<text x="101" y="55" class="eyebrow">ATOMCRYSTAL / VERIFIED PHYSICS</text>
<text x="48" y="106" font-size="39" font-weight="700" letter-spacing="-1.3">From microscopic ions to a verified surface response</text>
<text x="50" y="139" font-size="18" fill="#506a7a">A theory-selected coupling experiment, tested against explicit ions and Maxwell fields.</text>

<rect class="card" x="48" y="177" width="350" height="541" rx="16"/>
<rect class="card" x="422" y="177" width="830" height="541" rx="16"/>
<rect class="card" x="1276" y="177" width="476" height="541" rx="16"/>

<text x="72" y="211" class="eyebrow">01 / MICROSCOPIC ORIGIN</text>
<text x="72" y="247" font-size="23" font-weight="700">Stable polar dimers</text>
<path d="M129 294H152L159 284L173 304L187 284L201 304L215 284L229 304L243 284L250 294H275"
  fill="none" stroke="#8095a2" stroke-width="2"/>
<circle cx="119" cy="294" r="25" fill="#e89b78"/>
<circle cx="285" cy="294" r="25" fill="#188d97"/>
<text x="119" y="302" text-anchor="middle" font-size="27" style="fill:#fff">+</text>
<text x="285" y="302" text-anchor="middle" font-size="27" style="fill:#fff">−</text>
<text x="72" y="348" class="label">32 dimers · 64 microscopic ions</text>
<text x="72" y="374" class="label">Coulomb + short-range potential</text>
<line class="rule" x1="72" y1="395" x2="374" y2="395"/>
<text x="72" y="425" class="small">ACTUAL HESSIAN → LINEAR RESPONSE</text>
<text x="72" y="458" class="formula">U″(0) / μ = 2</text>
<text x="72" y="496" class="formula">ε(s) = (5 − s) / (2 − s)</text>
<rect x="70" y="518" width="306" height="77" rx="9" fill="#edf6f6"/>
<text x="85" y="542" class="small">CONTINUUM SURFACE PREDICTION</text>
<text x="85" y="577" font-size="25" font-weight="700">s = ω² = 3   ·   k∥ = √6</text>
<text x="72" y="629" font-size="15" font-weight="700">Direct illumination cannot match</text>
<text x="72" y="659" font-size="22">|k∥,vac| ≤ √3 &lt; √6</text>
<text x="72" y="692" class="small">ZERO BIAS · INFINITESIMAL RESPONSE</text>

<text x="446" y="211" class="eyebrow">02 / THEORY-SELECTED COUPLING</text>
<text x="446" y="247" font-size="24" font-weight="700">Supply the missing parallel momentum</text>
<text x="446" y="279" font-size="20">θ = 0    ·    m = 1    ·    Λ = 2π / √6    ·    k∥,in + G = √6</text>
<rect x="468" y="318" width="614" height="150" fill="#eff6fb"/>
<rect x="468" y="468" width="614" height="150" fill="url(#material)"/>
<rect x="468" y="393" width="614" height="150" fill="#068d94" opacity="0.035"/>
<g clip-path="url(#fieldClip)">
''']
    # Reconstruct the retained transverse Fourier intensity, cos²(Gx), for
    # three illustrative periods. The z-dependence is the certified data.
    for j, intensity in enumerate(profile):
        for i in range(96):
            transverse = math.cos(2*math.pi*3*(i+0.5)/96)**2
            opacity = 0.72*intensity*transverse
            svg.append(f'<rect x="{468+i*614/96:.3f}" y="{318+j*300/32:.3f}" '
                       f'width="6.407" height="9.385" fill="#008d98" opacity="{opacity:.5f}"/>')
    svg.append('''</g>
<path d="M468 318H1082M468 618H1082" stroke="#7b95a3" stroke-width="3"/>
<text x="482" y="342" class="small">VACUUM</text>
<text x="482" y="602" class="small">IONIC MATERIAL</text>
<text x="449" y="322" text-anchor="end" class="small">+2</text>
<text x="449" y="473" text-anchor="end" class="small">0</text>
<text x="449" y="622" text-anchor="end" class="small">−2</text>
<text x="447" y="307" text-anchor="end" class="small">z</text>
<text x="810" y="345" text-anchor="middle" font-size="14" style="fill:#496a7e">Uniform input channel</text>
<g stroke="#476779" stroke-width="1.8" marker-end="url(#arrow)">
  <path d="M695 357V396"/><path d="M810 357V396"/><path d="M925 357V396"/>
</g>
<text x="776" y="432" text-anchor="middle" font-size="18" font-weight="700" style="fill:#00676e">Surface-localized magnetic field</text>
<path d="M486 468H1064" stroke="#c57a30" stroke-width="1" stroke-dasharray="4 4"/>
''')
    points = [(486+i*578/240, 468-10*math.cos(2*math.pi*3*(18+i*578/240)/614))
              for i in range(241)]
    svg.append('<polyline points="'+' '.join(f'{x:.2f},{y:.2f}' for x,y in points)+'" '
               'fill="none" stroke="#c47729" stroke-width="2.8"/>')
    # Illustrative pairs only, deliberately not a purported 64-ion geometry.
    for row in range(2):
        for col in range(6):
            x, y = 531+col*92, 532+row*38
            svg.extend([
                f'<path d="M{x-13} {y}H{x+13}" stroke="#7b9aa3" stroke-width="1.5"/>',
                f'<circle cx="{x-15}" cy="{y}" r="8" fill="#dc9a7b"/>',
                f'<circle cx="{x+15}" cy="{y}" r="8" fill="#238c97"/>',
                f'<text x="{x-15}" y="{y+4}" text-anchor="middle" font-size="12" style="fill:#fff">+</text>',
                f'<text x="{x+15}" y="{y+4}" text-anchor="middle" font-size="12" style="fill:#fff">−</text>',
            ])
    svg.append('''<text x="1162" y="306" text-anchor="middle" font-size="14">|H(z)|²</text>
<rect x="1108" y="393" width="114" height="150" rx="3" fill="#eaf6f4"/>
<path d="M1108 318V618H1222" fill="none" stroke="#a2b6bf" stroke-width="1"/>
<path d="M1108 468H1222" stroke="#b0c8cc" stroke-dasharray="3 4"/>
''')
    outline = [(1108+105*v, 318+(j+0.5)*300/32) for j,v in enumerate(profile)]
    area = [(1108,318)] + outline + [(1108,618)]
    svg.append('<polygon points="'+' '.join(f'{x:.3f},{y:.3f}' for x,y in area)+
               '" fill="#00858a" opacity="0.14"/>')
    svg.append('<polyline points="'+' '.join(f'{x:.3f},{y:.3f}' for x,y in outline)+
               '" fill="none" stroke="#007d83" stroke-width="2.5"/>')
    svg.append('''<text x="1108" y="635" class="small">0</text>
<text x="1213" y="635" class="small" text-anchor="middle">1</text>
<text x="1162" y="655" text-anchor="middle" class="small">normalized</text>
<path d="M475 653H508" stroke="#c47729" stroke-width="3"/>
<text x="518" y="658" font-size="15" style="fill:#8c5725">Ideal prescribed source sheet · cos(Gx)</text>
<text x="446" y="695" class="small">Ions schematic; depth profile from the exact s = 3 certificate. Shading: |z| ≤ 1.</text>

<text x="1300" y="211" class="eyebrow">03 / WITHHELD MICROSCOPIC TEST</text>
<rect x="1300" y="235" width="428" height="65" rx="9" fill="#f0f3fa"/>
<text x="1320" y="260" class="small">PREDICTION FROZEN BEFORE THE SOLVE</text>
<text x="1320" y="286" font-size="20" font-weight="700">Drive s = 3</text>
<text x="1543" y="286" font-size="20" font-weight="700">Control s = 4</text>
<text x="1300" y="378" font-size="76" font-weight="700" letter-spacing="-3" style="fill:#007d83">≥ 4×</text>
<text x="1304" y="411" font-size="21" font-weight="700">interface magnetic intensity</text>
<text x="1304" y="449" font-size="23">I(3) ≥ 1</text>
<text x="1515" y="449" font-size="23">I(4) ≤ ¼</text>
<line class="rule" x1="1300" y1="473" x2="1728" y2="473"/>
<text x="1300" y="528" font-size="43" font-weight="700">≥ 60%</text>
<text x="1304" y="557" font-size="16">of magnetic intensity within |z| ≤ 1</text>
<text x="1304" y="581" font-size="15" style="fill:#007d83">Nonzero ionic response, checked explicitly</text>
<rect x="1300" y="603" width="428" height="67" rx="9" fill="#f2f6f8"/>
<text x="1316" y="629" font-size="20">3.01 ≤ ω<tspan baseline-shift="sub" font-size="12">micro</tspan><tspan baseline-shift="super" font-size="12">2</tspan> ≤ 3.012</text>
<text x="1316" y="655" font-size="20">0 &lt; ω<tspan baseline-shift="sub" font-size="12">micro</tspan> − √3 ≤ 0.004</text>
<text x="1300" y="696" class="small">I = H<tspan baseline-shift="sub" font-size="9">vac</tspan>(15)² + H<tspan baseline-shift="sub" font-size="9">mat</tspan>(15)² · equal generalized forcing</text>

<rect x="48" y="742" width="1704" height="94" rx="14" fill="#163447"/>
<text x="76" y="767" font-size="11" font-weight="700" letter-spacing="2" style="fill:#91b7c5">THE VERIFIED RESEARCH LOOP</text>
<g font-size="20" font-weight="600">
  <text x="76" y="807" style="fill:#fff">Derived effective law</text>
  <text x="346" y="807" style="fill:#7ec9c7">→</text>
  <text x="404" y="807" style="fill:#fff">Frozen prediction</text>
  <text x="650" y="807" style="fill:#7ec9c7">→</text>
  <text x="710" y="807" style="fill:#fff">Independent ionic–Maxwell solve</text>
  <text x="1135" y="807" style="fill:#7ec9c7">→</text>
  <text x="1196" y="807" style="fill:#a3e5d9">Lean-checked agreement</text>
</g>
<text x="50" y="871" font-size="14" style="fill:#526d7c">FINITE SYNTHETIC MATERIAL</text>
<text x="342" y="871" font-size="14" style="fill:#526d7c">LINEAR RESPONSE</text>
<text x="553" y="871" font-size="14" style="fill:#526d7c">IDEAL SOURCE COUPLER</text>
<text x="831" y="871" font-size="14" style="fill:#526d7c">NO REFLECTIVITY CLAIM</text>
<text x="1750" y="871" text-anchor="end" font-size="12" style="fill:#708894">verified_automated_surface_physics</text>
</svg>
''')
    return ''.join(svg)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check the committed SVG without writing")
    args = parser.parse_args()
    rendered = render()
    if args.check:
        if OUTPUT.read_text() != rendered:
            raise SystemExit("Banner differs from its reproducible source")
        print("Banner SVG reproduces exactly")
    else:
        OUTPUT.parent.mkdir(exist_ok=True)
        OUTPUT.write_text(rendered)
        print(OUTPUT)


if __name__ == "__main__":
    main()
