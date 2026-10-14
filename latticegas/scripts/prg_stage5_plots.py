"""Non-trusted plots of the one-shot Binder crossing-approximation correction."""
import json
from fractions import Fraction as F
from pathlib import Path

from grandcanonical_analysis import svg_lines

ROOT = Path(__file__).resolve().parent
RESULT = ROOT / "grandcanonical_results"


def main():
    first = json.loads((RESULT / "prg_stage4_quotient_analysis.json").read_text())
    second = json.loads((RESULT / "prg_stage5_analysis.json").read_text())
    cert = json.loads((RESULT / "prg_stage4_repair_certificate.json").read_text())
    high = {z["L"]: z for z in cert["new_cells"] if z["pair"] == "8_to_12"}
    x0, x1, x2 = F(41, 64), F(*second["fresh_pair8_r"]), F(9, 14)
    d0 = F(first["pairs"]["8_to_12"]["point_U4_difference_small_minus_large"])
    d1 = F(second["pairs"]["8_to_12"]["point_U4_difference_small_minus_large"])
    d2 = F(high[8]["U4_point"]) - F(high[12]["U4_point"])
    svg_lines(RESULT / "prg_stage5_Binder_approximation.svg",
              "Binder-only correction; guide lines are not confidence bounds",
              "U₄(8)−U₄(12)",
              {"fresh quotient points": [(float(x0), float(d0)), (float(x1), float(d1))],
               "9/14 design-only": [(float(x2), float(d2))],
               "zero": [(float(x0), 0), (float(x2), 0)]}, xlabel="r")
    for key, title, name in (("thermal_dimension_y_t_point", "thermal yₜ",
                              "prg_stage5_thermal_drift.svg"),
                             ("scattering_dimension_y_S_point", "scattering yₛ",
                              "prg_stage5_scattering_drift.svg")):
        small = first["pairs"]["4_to_6"][key]
        large0 = first["pairs"]["8_to_12"][key]
        large1 = second["pairs"]["8_to_12"][key]
        svg_lines(RESULT / name,
                  f"One-shot Binder-only correction of 8→12 {title} (exploratory)",
                  title, {"4→6 reference": [(float(x0), small), (float(x1), small)],
                          "8→12 approximation": [(float(x0), large0), (float(x1), large1)]},
                  xlabel="sampled r; both inside original certified crossing bracket")


if __name__ == "__main__":
    main()
