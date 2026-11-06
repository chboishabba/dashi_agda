"""DASHI source-to-force Maxwell-stress/dynamics synthetic physical regression."""
import json
import copy
import math
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_zhang2025_source_stress_dynamics as s


def bounded(n, u=0):
    return {"nominal": n, "bound": u, "evidence_receipt": "SYNTHETIC/reference"}


def bounded_force(n=0., u=0.):
    return {"nominal_N": n, "bound_N": u,
            "evidence_receipt": "SYNTHETIC/no true systematic evidence"}


def material():
    return {
        "mass_kg": bounded(1e-6),
        "electric_charge_C": bounded(1e-12),
        "polarizability_C_m2_V": bounded(0),
        "magnetic_susceptibility": bounded(0),
        "sample_volume_m3": bounded(1e-9),
        "spring_N_m": bounded(0),
        "damping_N_s_m": bounded(0),
        "equilibrium_x_m": bounded(0),
    }


def frame(t, position, e):
    return {
        "t_s": float(t),
        "t_s_bound": 0.,
        "time_evidence_receipt": "SYNTHETIC/clock",
        "x_m": bounded(position),
        "E_x_V_m": bounded(e),
        "E_V_m": [e, 0., 0.],
        "B_T": [0., 0., 0.],
        "grad_E2_x_V2_m3": bounded(0.),
        "grad_B2_x_T2_m": bounded(0.),
        "background_forces_N": {
            k: bounded_force() for k in s.DYNAMIC_BACKGROUND_CLASSES
        },
    }


def run(mode, acceleration=0.001):
    on = mode == "ON"
    electric_field = 1000. if on else 0.
    return {
        "source_mode": mode,
        "apparatus_id": "SYNTHETIC-ZHANG-B",
        "source_class": "zhang2025_toroid",
        "target_id": "SYNTHETIC-polystyrene",
        "axis": "x",
        "protocol_id": "SYNTHETIC/ONOFF",
        "calibration_id": "SYNTHETIC/cal",
        "instrument_id": "SYNTHETIC/camera",
        "run_id": "synthetic-" + mode,
        "raw_data_sha256": ("a" if on else "b") * 64,
        "frame_times_calibrated": True,
        "quasistatic_linear_response_justified": True,
        "material": material(),
        "frames": [
            frame(t, 0.5 * acceleration * t * t if on else 0., electric_field)
            for t in (0, 1, 2, 3, 4)
        ],
    }


def case():
    return {"data_kind": "synthetic", "on": run("ON"), "off": run("OFF")}


class ZhangPhysicalSourceRegression(unittest.TestCase):
    def test_repository_timed_fixture_executes_without_promotion(self):
        fixture = Path(__file__).resolve().parent / "fixtures" / "zhang2025_synthetic_translation_timed.json"
        case = json.loads(fixture.read_text(encoding="utf-8"))
        out = s.evaluate_pair(case)
        self.assertEqual(out["data_kind"], "synthetic")
        self.assertFalse(out["gravity_anomaly_established"])
        self.assertEqual(len(out["paired_frames"]), 3)

    def test_pure_electric_stress_has_correct_traction_and_trace(self):
        v = s.vacuum_maxwell_stress([1000, 0, 0], [0, 0, 0])
        energy = 0.5 * s.EPS0 * 1e6
        self.assertAlmostEqual(v["energy_density_J_m3"], energy)
        self.assertAlmostEqual(v["maxwell_traction_Pa"][0][0], energy)
        self.assertAlmostEqual(v["maxwell_traction_Pa"][1][1], -energy)
        self.assertAlmostEqual(v["lorentz_trace_Pa"], 0., places=15)
        self.assertFalse(v["material_stress_and_source_conservation_verified"])

    def test_orthogonal_e_b_has_poynting_flux(self):
        v = s.vacuum_maxwell_stress([20., 0., 0.], [0., 0.1, 0.])
        self.assertAlmostEqual(
            v["energy_flux_W_m2"][2], 2 / s.MAGNETIC_PERMEABILITY
        )
        self.assertAlmostEqual(v["energy_flux_W_m2"][0], 0.)
        self.assertEqual(len(v["maxwell_traction_Pa"]), 3)

    def test_quadratic_motion_is_explained_by_qE(self):
        r = s.evaluate_pair(case())
        self.assertEqual(len(r["paired_frames"]), 3)
        self.assertFalse(r["gravity_anomaly_established"])
        self.assertFalse(r["ordinary_model_is_complete"])
        self.assertFalse(r["material_stress_conservation_verified"])
        self.assertIsNone(r["confidence_interval_95"])
        self.assertFalse(r["all_frames_are_independent_replicates"])
        for p in r["paired_frames"]:
            a = p["on"]["acceleration_m_s2"]
            self.assertAlmostEqual(sum(a) / 2., .001, places=10)
            residual = p["paired_residual_N"]
            self.assertLess(abs(sum(residual) / 2.), 1e-18)

    def test_synthetic_unexplained_force_not_gravity(self):
        p = case()
        for f in p["on"]["frames"]:
            t = f["t_s"]
            f["x_m"] = bounded(.5 * .002 * t * t)
        r = s.evaluate_pair(p)
        self.assertTrue(all(x["zero_excluded"] for x in r["paired_frames"]))
        self.assertFalse(r["gravity_anomaly_established"])
        self.assertFalse(r["source_to_metric_solution_verified"])

    def test_missing_background_is_fatal(self):
        p = case()
        del p["on"]["frames"][2]["background_forces_N"]["thermal_drift"]
        with self.assertRaisesRegex(ValueError, "missing background"):
            s.evaluate_pair(p)

    def test_source_apparatus_mismatch_is_fatal(self):
        p = case()
        p["off"]["source_class"] = "zhang2025_HV_sphere"
        with self.assertRaisesRegex(ValueError, "same-object mismatch"):
            s.evaluate_pair(p)

    def test_target_mismatch_is_fatal(self):
        p = case()
        p["off"]["target_id"] = "different-object"
        with self.assertRaisesRegex(ValueError, "same-object mismatch"):
            s.evaluate_pair(p)

    def test_material_parameter_change_is_fatal(self):
        p = case()
        p["off"]["material"]["mass_kg"] = bounded(2e-6)
        with self.assertRaisesRegex(ValueError, "material/source"):
            s.evaluate_pair(p)

    def test_frames_must_be_aligned(self):
        p = case()
        p["off"]["frames"][3]["t_s"] = 3.1
        with self.assertRaisesRegex(ValueError, "not pair-aligned"):
            s.evaluate_pair(p)

    def test_uncalibrated_timestamps_are_rejected(self):
        p = case()
        p["on"]["frame_times_calibrated"] = False
        with self.assertRaisesRegex(ValueError, "frame_times_calibrated"):
            s.evaluate_pair(p)

    def test_nonphysical_negative_mass_rejected(self):
        p = case()
        p["on"]["material"]["mass_kg"] = bounded(1e-6, 2e-6)
        with self.assertRaisesRegex(ValueError, "positive lower mass"):
            s.evaluate_pair(p)

    def test_unjustified_linear_material_response_rejected(self):
        p = case()
        p["on"]["quasistatic_linear_response_justified"] = False
        with self.assertRaisesRegex(ValueError, "applicability"):
            s.evaluate_pair(p)

    def test_wrong_unit_suffix_rejected(self):
        p = case()
        p["on"]["material"]["electric_charge_C"] = bounded_force(1e-12)
        with self.assertRaisesRegex(ValueError, "finite number"):
            s.evaluate_pair(p)

    def test_missing_calibrated_gradient_rejected(self):
        p = case()
        del p["on"]["frames"][1]["grad_B2_x_T2_m"]
        with self.assertRaisesRegex(ValueError, "measurement interval"):
            s.evaluate_pair(p)

    def test_nonzero_clock_uncertainty_widens_force_residual(self):
        baseline = s.evaluate_pair(case())
        p = case()
        for mode in ("on", "off"):
            for f in p[mode]["frames"]:
                f["t_s_bound"] = .001
        expanded = s.evaluate_pair(p)
        old = baseline["paired_frames"][0]["paired_residual_N"]
        new = expanded["paired_frames"][0]["paired_residual_N"]
        self.assertLessEqual(new[0], old[0])
        self.assertGreaterEqual(new[1], old[1])

    def test_nonzero_E_uncertainty_widens_force_residual(self):
        baseline = s.evaluate_pair(case())
        p = case()
        for f in p["on"]["frames"]:
            f["E_x_V_m"] = bounded(1000., 100.)
        expanded = s.evaluate_pair(p)
        old = baseline["paired_frames"][0]["paired_residual_N"]
        new = expanded["paired_frames"][0]["paired_residual_N"]
        self.assertLess(new[0], old[0])
        self.assertGreater(new[1], old[1])

    def test_time_interval_overlap_rejected(self):
        p = case()
        for f in p["on"]["frames"]:
            f["t_s_bound"] = .51
        with self.assertRaisesRegex(ValueError, "timestamp intervals"):
            s.evaluate_pair(p)

    def test_source_not_allowed_to_claim_pais_instrument(self):
        p = case()
        p["on"]["source_class"] = "Pais-HFGWG"
        with self.assertRaisesRegex(ValueError, "actual Zhang rig"):
            s.evaluate_pair(p)

    def test_real_unverified_label_not_empirical_authority(self):
        p = case()
        p["data_kind"] = "real_unverified"
        r = s.evaluate_pair(p)
        self.assertEqual(r["data_kind"], "real_unverified")
        self.assertFalse(r["gravity_anomaly_established"])

    def test_bad_sha_and_duplicate_run_hash_rejected(self):
        p = case()
        p["on"]["raw_data_sha256"] = "x"
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            s.evaluate_pair(p)
        p = case()
        p["off"]["raw_data_sha256"] = p["on"]["raw_data_sha256"]
        with self.assertRaisesRegex(ValueError, "distinct run IDs"):
            s.evaluate_pair(p)

    def test_polarisation_force_uses_measured_gradient(self):
        p = case()
        p["on"]["material"]["electric_charge_C"] = bounded(0.)
        p["off"]["material"]["electric_charge_C"] = bounded(0.)
        p["on"]["material"]["polarizability_C_m2_V"] = bounded(1e-20)
        p["off"]["material"]["polarizability_C_m2_V"] = bounded(1e-20)
        for f in p["on"]["frames"]:
            f["grad_E2_x_V2_m3"] = bounded(2e11)
            t = f["t_s"]
            f["x_m"] = bounded(0.5 * 1e-3 * t * t)
        r = s.evaluate_pair(p)
        for row in r["paired_frames"]:
            self.assertLess(abs(sum(row["paired_residual_N"]) / 2.), 1e-18)

    def test_nonuniform_time_acceleration_derivative(self):
        p = case()
        times = (0, .3, 1.1, 1.4, 3.)
        for mode in ("on", "off"):
            for row, t in zip(p[mode]["frames"], times):
                row["t_s"] = float(t)
                row["x_m"] = bounded(.5 * .001 * t*t if mode == "on" else 0.)
        r = s.evaluate_pair(p)
        for row in r["paired_frames"]:
            self.assertLess(abs(sum(row["paired_residual_N"]) / 2.), 1e-18)


if __name__ == "__main__":
    unittest.main()
