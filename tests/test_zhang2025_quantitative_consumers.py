"""Regression: never convert a reported nominal parameter into gravity evidence."""
import math
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_zhang2025_quantitative_consumers as q


class QuantitativeConsumerTests(unittest.TestCase):
    def test_toroid_mass_range_and_95_ci_missing(self):
        r = q.report_2025()
        self.assertEqual(r["mass_g"]["ratio_max_to_min"], 40)
        self.assertIsNone(r["observed_acceleration_95CI"]["value"])
        self.assertIsNone(r["measured_force_N"]["value"])

    def test_50hz_rate_is_only_assumed_model(self):
        r = q.report_2025()
        k = r["conditional_sinusoidal_Bpeak_dBdt_peak_T_per_s"]
        self.assertEqual(k["kind"], "assumed_waveform_prediction_not_measurement")
        self.assertAlmostEqual(k["lo"], 2 * math.pi * 50 * .1)
        self.assertAlmostEqual(k["hi"], 2 * math.pi * 50 * .5)

    def test_magnetic_energy_density_not_force(self):
        r = q.report_2025()["conditional_magnetic_energy_density_J_per_m3"]
        self.assertGreater(r["hi"], r["lo"])
        self.assertEqual(r["kind"], "model_derived_local_field_energy_not_net_force")

    def test_author_3sigma_toroid_torque(self):
        r = q.report_2024()
        x = next(x for x in r["rows"] if x["test"] == "PTFE toroid torque")
        v = x["author_rule_3sigma_envelope"]
        self.assertAlmostEqual(v["lo"], -1.18)
        self.assertAlmostEqual(v["hi"], .44)
        self.assertTrue(v["contains_zero"])
        self.assertIsNone(x["formal_95CI"])

    def test_crossed_coil_is_not_promoted_by_two_sigma(self):
        x = next(x for x in q.report_2024()["rows"] if x["test"] == "crossed coil vertical")
        self.assertTrue(x["author_rule_3sigma_envelope"]["contains_zero"])
        self.assertIsNone(x["formal_95CI"])
        self.assertFalse(x["same_apparatus_as_zhang_toroid"])

    def test_heated_varistor_needs_nuisance_controls(self):
        x = next(x for x in q.report_2024()["rows"] if x["test"] == "heated varistor horizontal")
        self.assertIn("outgassing", x["condition"])

    def test_instrument_resolution_not_confidence_interval(self):
        r = q.report_2026()
        self.assertAlmostEqual(r["nominal_force_equivalent_N"], 9.80665e-7)
        self.assertIsNone(r["statistical_95CI"])

    def test_patent_and_pais_have_no_experimental_ci(self):
        x, y = q.report_patent_pais()
        self.assertEqual(x["nominal_VI_W"], .5)
        self.assertIsNone(x["experimental_force_95CI"])
        self.assertIsNone(y["experimental_GW_95CI"])

    def test_no_source_automatic_promotion(self):
        r = q.full_report()
        self.assertFalse(r["promotion"]["same_object_empirical_anomaly_available"])
        self.assertFalse(r["promotion"]["independent_Zhang_replication_available"])

    @staticmethod
    def config(deltas, **changes):
        data = dict(
            deltas=tuple(deltas), lower_hard_bound=-1., upper_hard_bound=1.,
            alpha=.05, repeated_independent_source_switches_declared=True,
            calibration_and_nuisance_bound_declared=True,
            same_apparatus_declared=True, evidence_locator="SYNTHETIC",
            data_kind="synthetic",
        )
        data.update(changes)
        return q.PairedCIInput(**data)

    def test_hoeffding_95ci_is_conditional_even_for_full_fixture(self):
        result = q.conditional_hoeffding_ci(self.config((0., 0., 0., 0.)))
        self.assertEqual(result["nominal_coverage"], .95)
        self.assertEqual(result["data_kind"], "synthetic")
        self.assertFalse(result["anomaly_or_gravity_established"])
        self.assertFalse(result["independence_and_hard_bound_verified"])
        self.assertLess(result["interval"][0], 0)
        self.assertGreater(result["interval"][1], 0)

    def test_missing_assumption_blocks_conditional_ci(self):
        result = q.conditional_hoeffding_ci(
            self.config((.01, .02), same_apparatus_declared=False)
        )
        self.assertEqual(result["kind"], "not_identifiable")
        self.assertIsNone(result["95CI"])

    def test_out_of_support_or_nan_rejected(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            q.conditional_hoeffding_ci(self.config((0, 1.1)))
        with self.assertRaisesRegex(ValueError, "finite"):
            q.conditional_hoeffding_ci(self.config((float("nan"),)))

    def test_incorrect_alpha_or_missing_locator_rejected(self):
        with self.assertRaisesRegex(ValueError, "alpha"):
            q.conditional_hoeffding_ci(self.config((.0,), alpha=0))
        with self.assertRaisesRegex(ValueError, "locator"):
            q.conditional_hoeffding_ci(self.config((.0,), evidence_locator=""))

    def test_empty_sample_rejected(self):
        with self.assertRaisesRegex(ValueError, "paired observations"):
            q.conditional_hoeffding_ci(self.config(()))

    def test_observational_domain_not_merged_across_apparatus(self):
        r = q.full_report()
        self.assertNotEqual(
            r["2025_toroid"]["apparatus_id"],
            r["2024_independent_steady_null"]["apparatus_id"],
        )
        self.assertNotEqual(
            r["2025_toroid"]["apparatus_id"],
            r["2026_independent_DC_null"]["apparatus_id"],
        )


    def test_mass_normalization_for_same_acceleration_is_conditionally_consistent(self):
        a = [
            dict(apparatus_id="SYNTHETIC/A", protocol_id="SYNTHETIC/ONOFF",
                 sample_id="paper", force_lo_N=4.5e-9, force_hi_N=5.5e-9,
                 mass_lo_kg=50e-6, mass_hi_kg=50e-6,
                 calibrated_force_and_ordinary_controls_declared=True,
                 data_locator="SYNTHETIC/paper"),
            dict(apparatus_id="SYNTHETIC/A", protocol_id="SYNTHETIC/ONOFF",
                 sample_id="aluminium", force_lo_N=1.8e-7, force_hi_N=2.2e-7,
                 mass_lo_kg=2e-3, mass_hi_kg=2e-3,
                 calibrated_force_and_ordinary_controls_declared=True,
                 data_locator="SYNTHETIC/aluminium"),
        ]
        r = q.conditional_material_independence_consumer(a)
        self.assertIsNotNone(r["shared_acceleration_interval"])
        self.assertFalse(r["common_acceleration_established"])
        self.assertFalse(r["gravitational_mechanism_established"])

    def test_material_consumer_rejects_distinct_protocol(self):
        rows = [
            dict(apparatus_id="A", protocol_id="ONOFF-1", sample_id="paper"),
            dict(apparatus_id="A", protocol_id="ONOFF-2", sample_id="metal"),
        ]
        with self.assertRaisesRegex(ValueError, "same apparatus/protocol"):
            q.conditional_material_independence_consumer(rows)

    def test_material_consumer_blocks_missing_classical_controls(self):
        rows = [
            dict(apparatus_id="A", protocol_id="P", sample_id="paper",
                 calibrated_force_and_ordinary_controls_declared=False),
            dict(apparatus_id="A", protocol_id="P", sample_id="metal",
                 calibrated_force_and_ordinary_controls_declared=True),
        ]
        self.assertEqual(
            q.conditional_material_independence_consumer(rows)["kind"], "not_identifiable"
        )

    def test_signed_force_mass_interval_handles_negative_force(self):
        lo, hi = q.acceleration_interval_from_force(-2., -1., 1., 2.)
        self.assertEqual((lo, hi), (-2., -.5))
        with self.assertRaisesRegex(ValueError, "positive mass"):
            q.acceleration_interval_from_force(0., 1., 0., 1.)


if __name__ == "__main__":
    unittest.main()
