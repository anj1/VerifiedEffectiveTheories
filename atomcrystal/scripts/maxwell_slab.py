#!/usr/bin/env python3
"""Untrusted finite staggered TM Maxwell-ion certificate generator.

The primitive frequency equations are curl E = omega H,
curl^T H = omega(E+P), (b-s)u=E, P=3*f*u.
Eliminating the explicit ionic coordinates gives the tridiagonal H operator
used here. Lean must check that elimination and every accepted enclosure.
"""
import json
import argparse
from fractions import Fraction as Q
from pathlib import Path


def determinant(s, n=8, spacing=Q(1, 4), b=Q(2)):
    t = 1 / spacing**2
    em = 1 + 3 / (b - s)
    ei = 1 + Q(3, 2) / (b - s)
    edges = [Q(0)] + [t] * (n - 1) + [t / ei] + [t / em] * (n - 1) + [Q(0)]
    normals = [Q(6)] * n + [6 / em] * n
    d0, d1 = Q(1), Q(0)
    for j in range(2*n):
        diag = edges[j] + edges[j+1] + normals[j] - s
        d0, d1 = (diag * d0 - edges[j]**2 * d1), d0
    return d0


def primitive_witness(s, n, spacing, b=Q(2)):
    """Reconstruct explicit fields and ionic coordinates; output is empirical."""
    inv_h = 1 / spacing
    t = inv_h**2
    em, ei = 1 + 3 / (b-s), 1 + Q(3, 2) / (b-s)
    def profile(q):
        values = [Q(1), q-1]
        for _ in range(2, n):
            values.append(q*values[-1]-values[-2])
        return values
    pv = profile(2+(6-s)/t)
    pm = profile(2+(6-em*s)/t)
    coupling = t/ei
    left = (t+6-s+coupling)*pv[-1]-t*pv[-2]
    v = [x/pv[-1] for x in pv]
    m = [left*x/(coupling*pv[-1]*pm[-1]) for x in pm]
    ev = [inv_h*(v[j+1]-v[j]) for j in range(n-1)]
    et = [inv_h*(m[j+1]-m[j])/em for j in range(n-1)]
    en = [x/em for x in m]
    ut = [x/(b-s) for x in et]
    un = [x/(b-s) for x in en]
    eface = inv_h*(v[-1]-m[-1])/ei
    uface = eface/(b-s)
    residuals = [-inv_h*ev[0]+6*v[0]-s*v[0],
                 -inv_h*et[0]+6*en[0]-s*m[0],
                 inv_h*(ev[-1]+eface)+6*v[-1]-s*v[-1],
                 inv_h*(et[-1]-eface)+6*en[-1]-s*m[-1]]
    for j in range(n-2):
        residuals.extend([inv_h*(ev[j]-ev[j+1])+6*v[j+1]-s*v[j+1],
                          inv_h*(et[j]-et[j+1])+6*en[j+1]-s*m[j+1]])
    total = sum(x*x for x in v+m)
    outer = sum(v[j]**2+m[j]**2 for j in range(n//2))
    return {
        "classification": "empirical reconstructed primitive fields at a rational near-root",
        "indexing": "outer boundary to interface; normal electric and ionic components divided by sqrt(6)",
        "vacuum_magnetic": list(map(float, v)),
        "material_magnetic": list(map(float, m)),
        "vacuum_tangential_electric": list(map(float, ev)),
        "material_tangential_electric": list(map(float, et)),
        "material_normal_electric": list(map(float, en)),
        "material_tangential_ionic": list(map(float, ut)),
        "material_normal_ionic": list(map(float, un)),
        "interface_electric": float(eface),
        "interface_ionic_normalized": float(uface),
        "max_faraday_residual": float(max(map(abs, residuals))),
        "inner_half_magnetic_energy_fraction": float(1-outer/total),
        "proof_status": "These samples are not proof; Lean reconstructs a mode at an exact IVT root."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--prediction", default="artifacts/maxwell_prediction.json")
    args = parser.parse_args()
    p = json.loads((Path(__file__).parents[1] / args.prediction).read_text())
    def evaluate(s):
        return determinant(s, p["vacuum_cells"], Q(p["spacing"]))
    lo, hi = map(Q, p["predicted_squared_frequency_interval"])
    f0, f1 = evaluate(lo), evaluate(hi)
    bracket = None
    if f0 * f1 < 0:
        a, b = lo, hi
        for _ in range(40):
            mid = (a+b)/2
            if evaluate(a)*evaluate(mid) <= 0:
                b = mid
            else:
                a = mid
        bracket = [str(a), str(b)]
    print(json.dumps({
        "classification": "untrusted empirical output and certificate proposal",
        "prediction": p,
        "endpoint_signs": [int(f0 > 0)-int(f0 < 0), int(f1 > 0)-int(f1 < 0)],
        "root_bracket": bracket,
        "approx_root": None if bracket is None else float((a+b)/2),
        "characteristic_at_prediction": str(evaluate(Q(3))),
        "primitive_witness": None if bracket is None else
          primitive_witness((a+b)/2, p["vacuum_cells"], Q(p["spacing"]))
    }, indent=2))
