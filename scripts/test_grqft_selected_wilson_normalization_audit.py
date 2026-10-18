#!/usr/bin/env python3
"""Exact-rational fixture tests. These fixtures are not physical CMP119 data."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "wilson_audit", Path(__file__).with_name("grqft_selected_wilson_normalization_audit.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def fixture(factor=1):
    return {
        "provenance": {
            "source_identifier": "toy-not-CMP119", "source_revision": "test1",
            "source_locator": "toy:fixture", "action_identifier": "toy-wilson",
            "coupling_identifier": "toy-g", "cutoff": "toy",
            "plaquette_basis": "Wplus=sum(1-ReTrU/2)",
            "trace_convention": "SU2-toy", "coefficient_origin": "toy-premise"
        },
        "bare_coefficient_convention":
            "unit_inverse_square" if factor == 1 else "standard_SU2_four_inverse_square",
        "g_squared": "1/2", "inverse_g_squared": "2",
        "selected_exponent_sign": "log_density=-action",
        "configurations": [
            {"configuration_id": "a", "plaquette_normalized_real_traces": ["0"],
             "exponent_nonwilson_sectors":
                 {"E": "1", "R": "1/2", "B": "0", "vacuum": "-1/2"},
             "selected_total_log_density_exponent": str(1 - 2 * factor)},
            {"configuration_id": "b",
             "plaquette_normalized_real_traces": ["-1", "1/2"],
             "exponent_nonwilson_sectors":
                 {"E": "2", "R": "0", "B": "0", "vacuum": "0"},
             "selected_total_log_density_exponent": str(2 - 5 * factor)}
        ]
    }


class LiteralWilsonNormalizationAuditTests(unittest.TestCase):
    def test_unit_basis_exact(self):
        result = module.audit(fixture())
        self.assertEqual(result["recovered_multi_probe_coefficient"], "-2")
        self.assertFalse(result["published_cmp119_source_identification_proved"])

    def test_standard_su2_bare_coefficient_exact(self):
        self.assertEqual(module.audit(fixture(4))["recovered_multi_probe_coefficient"], "-8")

    def test_factor_four_mismatch_rejected(self):
        source = fixture()
        source["bare_coefficient_convention"] = "standard_SU2_four_inverse_square"
        with self.assertRaisesRegex(ValueError, "mismatch"):
            module.audit(source)

    def test_inconsistent_probes_rejected(self):
        source = fixture()
        source["configurations"][1]["selected_total_log_density_exponent"] = "-7"
        with self.assertRaisesRegex(ValueError, "disagree"):
            module.audit(source)

    def test_nonwilson_sector_mismatch_rejected(self):
        source = fixture()
        source["configurations"][0]["exponent_nonwilson_sectors"]["E"] = "0"
        with self.assertRaisesRegex(ValueError, "disagree"):
            module.audit(source)

    def test_zero_cost_cannot_fix_coefficient(self):
        source = fixture()
        for config in source["configurations"]:
            config["plaquette_normalized_real_traces"] = ["1"]
            config["selected_total_log_density_exponent"] = (
                "1" if config["configuration_id"] == "a" else "2")
        with self.assertRaisesRegex(ValueError, "Two nonzero"):
            module.audit(source)

    def test_invalid_su2_trace_rejected(self):
        source = fixture()
        source["configurations"][0]["plaquette_normalized_real_traces"] = ["2"]
        with self.assertRaisesRegex(ValueError, "outside"):
            module.audit(source)

    def test_invalid_inverse_coupling_rejected(self):
        source = fixture()
        source["inverse_g_squared"] = "3"
        with self.assertRaisesRegex(ValueError, "inverse product"):
            module.audit(source)

    def test_unknown_basis_rejected(self):
        source = fixture()
        source["provenance"]["plaquette_basis"] = "unknown"
        with self.assertRaisesRegex(ValueError, "Unrecognized"):
            module.audit(source)


if __name__ == "__main__":
    unittest.main()
