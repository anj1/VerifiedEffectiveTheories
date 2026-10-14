"""Non-trusted visualization of narrowed crossings and finite-size quotients."""
import json
import math
from fractions import Fraction as F
from pathlib import Path

from grandcanonical_analysis import svg_lines

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "grandcanonical_results"


def main():
    cert = json.loads((OUT / "prg_stage4_repair_certificate.json").read_text())
    quot = json.loads((OUT / "prg_stage4_quotient_analysis.json").read_text())
    old = json.loads((OUT / "prg_covcert.json").read_text())
    old_high = json.loads((OUT / "prg_covcert2.json").read_text())
    points = cert["new_cells"] + [z for z in old["cells"] if z["r"] == [7, 11]] + old_high["cells"]
    for pair, sizes in (("4_to_6", (4, 6)), ("8_to_12", (8, 12))):
        lines = {}
        selected = [z for z in points if z["L"] in sizes and
                    (z.get("pair") == pair or pair == "8_to_12" and
                     z["r"] in ([7, 11], [20, 31]))]
        for L in sizes:
            subset = sorted((z for z in selected if z["L"] == L),
                            key=lambda z: z["r"][0] / z["r"][1])
            for field, label in (("F_point", "point"),
                                 ("F_interval", "confidence lower"),
                                 ("F_interval", "confidence upper")):
                vals = []
                for z in subset:
                    v = z[field]
                    if isinstance(v, list):
                        v = v[0 if label.endswith("lower") else 1]
                    vals.append((z["r"][0] / z["r"][1], float(F(v))))
                lines[f"L={L} {label}"] = vals
        if pair == "8_to_12":
            lo, hi = F(7, 11), F(20, 31)
        else:
            lo, hi = [F(*x) for x in cert[f"crossing_{pair}_bracket"]]
        lines["zero"] = [(float(lo), 0), (float(hi), 0)]
        title = ("4→6 repaired Binder signs" if pair == "4_to_6" else
                 "8→12 Binder signs; 9/14 L=12 unresolved")
        svg_lines(OUT / f"prg_stage4_crossing_{pair}.svg",
                  title + " (lines guide only)",
                  "F=E[m⁴]−cE[m²]²", lines, xlabel="r; c differs by endpoint")

    log_s = math.log(1.5)
    for key, ylabel, filename in (("y_t", "thermal dimension y_t",
                                   "prg_stage4_thermal_dimensions.svg"),
                                  ("y_S", "scattering dimension y_S",
                                   "prg_stage4_scattering_dimensions.svg")):
        lines = {"point": [], "bootstrap exploratory lower": [],
                 "bootstrap exploratory upper": []}
        if key == "y_S":
            lines["conditional S lower"] = []
            lines["conditional S upper"] = []
        for name, L in (("4_to_6", 4), ("8_to_12", 8)):
            z = quot["pairs"][name]
            lines["point"].append((L, z["thermal_dimension_y_t_point"] if key == "y_t"
                                   else z["scattering_dimension_y_S_point"]))
            bl, bu = z["bootstrap_95_exploratory"][key]
            lines["bootstrap exploratory lower"].append((L, bl))
            lines["bootstrap exploratory upper"].append((L, bu))
            if key == "y_S":
                ql, qu = (F(x) for x in z["Q_S_conditional_95_familywise_interval"])
                lines["conditional S lower"].append((L, math.log(float(ql)) / log_s))
                lines["conditional S upper"].append((L, math.log(float(qu)) / log_s))
        svg_lines(OUT / filename, f"Two 3/2 scale transformations: {ylabel}",
                  ylabel, lines, xlabel="smaller lattice size L")


if __name__ == "__main__":
    main()
