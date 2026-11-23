"""Regression checks for the superconductivity effective models."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from certify import hamiltonian
from crystal_bcs import read_crystal
from dfpt_certificate import matrix_witness
from dfpt_full_assembly import assemble_full_sector
from dfpt_harmonic import pair_transfers
from dfpt_shell_certificate import lean_source as shell_lean_source
from dfpt_shell_eft import electronic_sector, exact_ground, parse_case, run
from four_site_eft import mean_field_free_energy
from two_shell_prediction import G, RADII, cubic_parity_matched_coupling


ARTIFACTS = Path(__file__).resolve().parents[1] / "artifacts"


class EFTRegressions(unittest.TestCase):
    def test_two_shell_scalar_matches_each_parity_through_cubic_order(self):
        def parity_coefficients(levels, odd):
            sectors = []
            for n in (odd - 1, odd, odd + 1):
                kinetic = hamiltonian(levels, 0, n)
                hop = hamiltonian(levels, 1, n)
                head = min(range(len(kinetic)), key=lambda i: kinetic[i][i])
                weights = {
                    i: Q(1, kinetic[i][i] - kinetic[head][head])
                    for i in range(len(kinetic)) if i != head and hop[head][i]
                }
                loops = sum(wi * wj for i, wi in weights.items() for j, wj in weights.items()
                            if i != j and hop[i][j])
                sectors.append((Q(hop[head][head] - kinetic[head][head]), -sum(weights.values()), -loops))
            return tuple(o - (e + ne) / 2 for e, o, ne in zip(*sectors, strict=True))

        linear, quadratic, cubic = parity_coefficients((-1, 0, 1), 3)
        for r, s in RADII:
            with self.subTest(r=r, s=s):
                full_linear, full_quadratic, full_cubic = parity_coefficients((-s, -r, -1, 0, 1, r, s), 7)
                self.assertEqual(full_linear, linear)
                a = (full_quadratic - quadratic) / linear
                b = (full_cubic - cubic - 2 * a * quadratic) / linear
                for g in (G, G / 2):
                    self.assertEqual(cubic_parity_matched_coupling(g, (r, s)), g + g**2 * a + g**3 * b)

    def test_signed_component_has_a_lower_bound_witness(self):
        case = parse_case(json.loads((ARTIFACTS / "dfpt_harmonic_example.json").read_text()))
        _, _, matrix = assemble_full_sector(case, 2)
        tolerance = Q(1, 10**9)
        endpoints = exact_ground(matrix, tolerance)
        _, _, _, _, squares = matrix_witness(case, 2, endpoints, tolerance)
        self.assertTrue(squares)
        self.assertTrue(all(pivot > 0 and vector for pivot, vector in squares))

    def test_zero_source_free_energy_encloses_high_precision_value(self):
        crystal = read_crystal(ARTIFACTS / "crystal_bcs_example.json")
        t = Q(1, 2)
        with localcontext() as context:
            context.prec = 85
            levels = [Decimal(x.numerator) / x.denominator for x in crystal.xi]
            # The minimum has zero gap at this temperature and zero source.
            reference = Q(sum(x - abs(x) - (1 + (-2*abs(x)).exp()).ln() for x in levels))
        retained = json.loads((ARTIFACTS / "four_site_eft.json").read_text())
        row = next(row for row in retained["temperatures"] if Q(row["kbt_mev"]) == t)
        for lo, hi in (mean_field_free_energy(crystal.xi, crystal.coupling, Q(0), t),
                       tuple(map(Q, row["free_energy_at_zero_mev"]["bcs"]))):
            self.assertLessEqual(lo, reference)
            self.assertLessEqual(reference, hi)

    def test_full_assembly_from_projected_and_cartesian_vertices(self):
        data = {
            "levels_mev": [-1, 2],
            "screening_convention": "Test interaction",
            "screened_density_terms": [[0, 0, 0, 1, 3]],
            "screened_scattering_terms": [
                [[[1, 1], [1, 0]], [[0, 1], [0, 0]], "1/3"],
                [[[0, 0], [0, 1]], [[1, 0], [1, 1]], "1/3"],
            ],
            "upstream_sector_error_mev": 0,
            "mass_weighted_modes": [{"omega_squared_mev2": 4, "potential_derivative": [
                [0, 0, 2], [0, 1, 1], [1, 1, -1],
            ]}],
        }
        case = parse_case(data)
        projected = assemble_full_sector(case, 2)
        normal, modes, instantaneous = projected
        # The first and last determinants are the doubly occupied orbitals.
        self.assertEqual(normal[0], {0: 1, 5: Q(-1, 3)})
        self.assertEqual(modes[0][1][0], {0: 4, 2: 1, 3: -1})
        self.assertEqual(instantaneous[0], {0: Q(-5, 4), 2: Q(-5, 8), 3: Q(5, 8), 5: Q(-7, 12)})
        self.assertEqual(electronic_sector(case, 2)[2], instantaneous)

        data["mass_weighted_cartesian_derivatives"] = [[[0, 0, 2], [0, 1, "5/3"]],
                                                       [[0, 0, 1], [1, 1, "-5/4"]]]
        data["mass_weighted_modes"] = [{"omega_squared_mev2": 4, "eigenvector": ["3/5", "4/5"]}]
        case = parse_case(data)
        self.assertEqual(assemble_full_sector(case, 2), projected)
        self.assertEqual(electronic_sector(case, 2)[2], instantaneous)
        self.assertEqual(pair_transfers(data)["transfers"], [{
            "orbitals": [0, 1],
            "screened_mev": "-1/3",
            "phonon_mev": "-1/4",
            "instantaneous_mev": "-7/12",
            "modes": [{"index": 0, "mev": "-1/4"}],
        }])

    def test_shell_certificate_uses_only_reduction_witnesses(self):
        path = ARTIFACTS / "dfpt_5_orbital_example.json"
        frozen = json.loads((ARTIFACTS / "dfpt_5_orbital_prediction.json").read_text())
        with (
            patch("dfpt_shell_eft.assemble_full_sector", side_effect=AssertionError),
            patch("dfpt_shell_eft.exact_ground", side_effect=AssertionError),
        ):
            certificate = shell_lean_source(path, frozen, "DFPTFive")
        expected = ARTIFACTS.parent / "Grain" / "DFPTFivePrediction.lean"
        self.assertEqual(certificate, expected.read_text())

    def test_edge_fillings_and_independent_validation(self):
        data = json.loads((ARTIFACTS / "dfpt_5_orbital_example.json").read_text())
        with TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            for odd, edge in ((1, "0"), (9, "10")):
                with self.subTest(odd_electrons=odd):
                    data["odd_electrons"] = odd
                    path.write_text(json.dumps(data))
                    predicted = run(path)["sectors"]
                    with patch("dfpt_shell_eft.electronic_sector", side_effect=AssertionError):
                        validated = run(path, validate=True)["sectors"]
                    for name, sectors in predicted.items():
                        self.assertEqual(sectors[edge]["configurations"], 1)
                        self.assertEqual(sectors[edge]["active_configurations"], 1)
                        for n, quantities in validated[name].items():
                            for quantity, (lo, hi) in quantities.items():
                                predicted_lo, predicted_hi = sectors[n][quantity]
                                self.assertLessEqual(max(lo, predicted_lo), min(hi, predicted_hi))


if __name__ == "__main__":
    unittest.main()
