"""Non-trusted SVG visualizations for the PRG experiment."""
import json
import math
from fractions import Fraction
from pathlib import Path

from grandcanonical_analysis import svg_lines

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "grandcanonical_results"


def main():
    scout = json.loads((OUT / "prg_scout.json").read_text())
    refine = json.loads((OUT / "prg_refine.json").read_text())
    refine2 = json.loads((OUT / "prg_refine2.json").read_text())
    analysis = json.loads((OUT / "prg_analysis.json").read_text())
    sw = {8: [], 12: []}
    for dataset in (scout, refine, refine2):
        for key, result in dataset["results"].items():
            r = float(eval_fraction(key))
            for L in (8, 12):
                sw[L].append((r, result[str(L)]["U4"]))
    exact = {8: [], 12: []}
    for point in analysis["points"].values():
        if point["L"] in exact and "U4" in point:
            r = point["r"][0] / point["r"][1]
            exact[point["L"]].append((r, point["U4"]))
    svg_lines(OUT / "prg_binder_curves.svg", "8→12 Binder crossing: scout and exact samples",
              "U₄", {"SW scout L=8": sw[8], "SW scout L=12": sw[12],
                     "CFTP L=8": exact[8], "CFTP L=12": exact[12]})

    diffs = []
    lo = []
    hi = []
    for key, data in analysis["endpoint_comparisons"].items():
        x = float(eval_fraction(key))
        diffs.append((x, data["delta_U4_8_minus_12"]))
        a, b = data["bootstrap_percentile_95_exploratory"]
        lo.append((x, a))
        hi.append((x, b))
    svg_lines(OUT / "prg_binder_difference.svg", "8−12 Binder difference: exploratory uncertainty",
              "U₄(8) − U₄(12)", {"estimate": diffs, "bootstrap 2.5%": lo,
                                  "bootstrap 97.5%": hi})

    sizes = [4, 6, 8, 12]
    slope = []
    scatter = []
    for L in sizes:
        p = analysis["points"][f"L{L}_r16_25"]
        slope.append((math.log(L), math.log(abs(p["binder_log_r_slope"]))))
        scatter.append((math.log(L), math.log(p["S_spin_kmin"])))
    svg_lines(OUT / "prg_log_scaling.svg", "Finite-size scaling at r=16/25 (not a certified crossing)",
              "log observable", {"log |dU₄/dlog r|": slope, "log S_spin(k_min)": scatter},
              xlabel="log L")

    eta = [(4, analysis["pseudo_crossing_quotients"]["4_to_6_r16_25"]["eta_proxy"]),
           (8, analysis["pseudo_crossing_quotients"]["8_to_12_r16_25"]["eta_proxy"])]
    nu = [(4, analysis["pseudo_crossing_quotients"]["4_to_6_r16_25"]["nu_proxy"]),
          (8, analysis["pseudo_crossing_quotients"]["8_to_12_r16_25"]["nu_proxy"])]
    svg_lines(OUT / "prg_quotient_drift.svg", "Effective quotient drift (pseudo-crossing proxy)",
              "effective exponent proxy", {"nu proxy": nu, "eta proxy": eta},
              xlabel="smaller lattice size L")
    covpath = OUT / "prg_covcert.json"
    if covpath.exists():
        cov = json.loads(covpath.read_text())
        selected = [z for z in cov["cells"] if z["r"] == [7, 11]]
        cov2path = OUT / "prg_covcert2.json"
        if cov2path.exists():
            selected += json.loads(cov2path.read_text())["cells"]
        else:
            selected += [z for z in cov["cells"] if z["r"] == [20, 31]]
        lines = {}
        for L in (8, 12):
            cells = sorted((z for z in selected if z["L"] == L),
                           key=lambda z: z["r"][0] / z["r"][1])
            lines[f"L={L} estimate"] = [(z["r"][0] / z["r"][1],
                                          float(Fraction(z["F_point"]))) for z in cells]
            lines[f"L={L} familywise lower"] = [(z["r"][0] / z["r"][1],
                                           float(Fraction(z["F_interval"][0]))) for z in cells]
            lines[f"L={L} familywise upper"] = [(z["r"][0] / z["r"][1],
                                           float(Fraction(z["F_interval"][1]))) for z in cells]
        lines["zero"] = [(7 / 11, 0), (20 / 31, 0)]
        svg_lines(OUT / "prg_covariance_signs.svg",
                  "Endpoint-specific Binder sign bounds; joining lines are not interpolation",
                  "F = E[m⁴] − c(r) E[m²]²", lines, xlabel="r (threshold c differs by endpoint)")
        print("wrote five SVG plots")
    else:
        print("wrote four SVG plots")


def eval_fraction(text):
    a, b = text.split("/")
    return int(a) / int(b)


if __name__ == "__main__":
    main()
