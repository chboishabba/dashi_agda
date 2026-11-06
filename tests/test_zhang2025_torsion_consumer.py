"""Finite-difference torsion source tests, synthetic only."""
import math
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import check_zhang2025_torsion_consumer as t
from check_zhang2025_source_stress_dynamics import Interval


def bounded(n=0., u=0.):
    return {"nominal": float(n), "bound": float(u),
            "evidence_receipt": "SYNTHETIC/fixture"}


def material():
    return {
        "inertia_kg_m2": bounded(1e-7),
        "damping_Nm_s_rad": bounded(0.),
        "torsion_Nm_rad": bounded(0.),
        "zero_angle_rad": bounded(0.),
        "electric_polarizability_anisotropy_C_m2_V": bounded(2e-16),
        "magnetic_susceptibility_anisotropy": bounded(0.),
        "sample_volume_m3": bounded(1e-8),
    }


def frame(ts, mode, acceleration=.001):
    active = mode == "ON"
    theta = .5 * acceleration * ts*ts if active else 0.
    phi = theta + math.pi/4 if active else 0.
    e = 1000. if active else 0.
    return {
        "t_s": float(ts),
        "theta_rad": bounded(theta),
        "E_V_m": [e * math.cos(phi), e * math.sin(phi), 0.],
        "B_T": [0., 0., 0.],
        "E2_V2_m2": bounded(e*e, 1e-8 if active else 0.),
        "B2_T2": bounded(0.),
        "electric_axis_angle_rad": bounded(phi),
        "magnetic_axis_angle_rad": bounded(0.),
        "background_torques_Nm": {
            k: bounded(0.) for k in t.TORQUE_BACKGROUND_CLASSES
        },
    }


def run(mode):
    return {
        "source_mode": mode,
        "apparatus_id": "SYNTHETIC/HV-sphere",
        "source_class": "zhang2025_HV_sphere",
        "target_id": "SYNTHETIC/polymer-ball",
        "axis": "vertical-torsion",
        "protocol_id": "SYNTHETIC/pulse-sweep",
        "calibration_id": "SYNTHETIC/angle-video",
        "instrument_id": "SYNTHETIC/camera",
        "run_id": mode+"-synthetic",
        "raw_data_sha256": ("a" if mode == "ON" else "b")*64,
        "frame_times_calibrated": True,
        "linear_quasistatic_anisotropy_justified": True,
        "material": material(),
        "frames": [frame(x, mode) for x in (0, 1, 2, 3, 4)],
    }


def case():
    return {"data_kind": "synthetic", "on": run("ON"), "off": run("OFF")}


class TorsionTests(unittest.TestCase):
    def test_sine_interior_critical_extrema(self):
        i = t.sine_interval(Interval(0., math.pi))
        self.assertAlmostEqual(i.hi, 1.)
        self.assertGreaterEqual(i.lo, -1e-15)
        i = t.sine_interval(Interval(0., 2*math.pi))
        self.assertEqual(i, Interval(-1., 1.))

    def test_electric_alignment_torque_explains_synthetic_rotation(self):
        r = t.evaluate_pair(case())
        self.assertEqual(r["consumer"], "rotation_or_thread_torsion_not_weight_or_spacetime")
        self.assertEqual(len(r["paired_frames"]), 3)
        for row in r["paired_frames"]:
            residual = row["paired_signed_torque_residual_Nm"]
            self.assertLess(abs(sum(residual)/2.), 1e-17)
            a = row["on"]["angular_acceleration_rad_s2"]
            self.assertAlmostEqual(sum(a)/2., .001)
        self.assertFalse(r["gravity_anomaly_established"])
        self.assertFalse(r["metric_perturbation_measured"])

    def test_no_independent_frame_confidence_interval(self):
        r = t.evaluate_pair(case())
        self.assertIsNone(r["confidence_interval_95"])
        self.assertFalse(r["frames_are_independent_replicates"])

    def test_unexplained_torque_does_not_prove_gravity(self):
        p = case()
        for f in p["on"]["frames"]:
            ts = f["t_s"]
            f["theta_rad"] = bounded(.5 * .003 * ts*ts)
            phi = f["theta_rad"]["nominal"] + math.pi / 4
            f["electric_axis_angle_rad"] = bounded(phi)
            f["E_V_m"] = [1000*math.cos(phi), 1000*math.sin(phi), 0.]
        r = t.evaluate_pair(p)
        self.assertTrue(any(row["zero_excluded"] for row in r["paired_frames"]))
        self.assertFalse(r["gravity_anomaly_established"])

    def test_missing_torque_nuisance_is_rejected(self):
        p = case()
        del p["on"]["frames"][1]["background_torques_Nm"]["thread_asymmetry"]
        with self.assertRaisesRegex(ValueError, "missing torque backgrounds"):
            t.evaluate_pair(p)

    def test_source_apparatus_is_strict(self):
        p = case()
        p["off"]["source_class"] = "zhang2025_toroid"
        with self.assertRaisesRegex(ValueError, "same-object torsion mismatch"):
            t.evaluate_pair(p)

    def test_material_inertia_mismatch_is_rejected(self):
        p = case()
        p["off"]["material"]["inertia_kg_m2"] = bounded(1e-6)
        with self.assertRaisesRegex(ValueError, "same-object torsion mismatch"):
            t.evaluate_pair(p)

    def test_E2_outside_vector_uncertainty_rejected(self):
        p = case()
        p["on"]["frames"][1]["E2_V2_m2"] = bounded(99.)
        with self.assertRaisesRegex(ValueError, "outside stated E2"):
            t.evaluate_pair(p)

    def test_angle_source_direction_inconsistency_rejected(self):
        p = case()
        p["on"]["frames"][1]["electric_axis_angle_rad"] = bounded(0.)
        with self.assertRaisesRegex(ValueError, "angle disagrees"):
            t.evaluate_pair(p)

    def test_out_of_plane_B_rejected(self):
        p = case()
        p["on"]["frames"][1]["B_T"] = [0., 0., .1]
        p["on"]["frames"][1]["B2_T2"] = bounded(.01)
        with self.assertRaisesRegex(ValueError, "planar torsion"):
            t.evaluate_pair(p)

    def test_zero_inertia_rejected(self):
        p = case()
        for mode in ("on", "off"):
            p[mode]["material"]["inertia_kg_m2"] = bounded(0.)
        with self.assertRaisesRegex(ValueError, "strictly positive"):
            t.evaluate_pair(p)

    def test_negative_thread_stiffness_rejected(self):
        p = case()
        p["on"]["material"]["torsion_Nm_rad"] = bounded(-1e-10)
        with self.assertRaisesRegex(ValueError, "nonnegative"):
            t.evaluate_pair(p)

    def test_timestamps_nonmonotone_rejected(self):
        p = case()
        p["on"]["frames"][3]["t_s"] = 1.
        with self.assertRaisesRegex(ValueError, "strictly increasing"):
            t.evaluate_pair(p)

    def test_frame_time_pairing_rejected(self):
        p = case()
        p["off"]["frames"][3]["t_s"] = 3.1
        with self.assertRaisesRegex(ValueError, "time grids"):
            t.evaluate_pair(p)

    def test_bad_hash_or_same_raw_identifier_rejected(self):
        p = case()
        p["on"]["raw_data_sha256"] = "garbage"
        with self.assertRaisesRegex(ValueError, "SHA-256"):
            t.evaluate_pair(p)
        p = case()
        p["on"]["raw_data_sha256"] = p["off"]["raw_data_sha256"]
        with self.assertRaisesRegex(ValueError, "distinct IDs"):
            t.evaluate_pair(p)

    def test_uncalibrated_or_missing_input_rejected(self):
        p = case()
        p["on"]["frame_times_calibrated"] = False
        with self.assertRaisesRegex(ValueError, "calibrated"):
            t.evaluate_pair(p)
        p = case()
        del p["on"]["frames"][2]["theta_rad"]
        with self.assertRaisesRegex(ValueError, "interval object"):
            t.evaluate_pair(p)

    def test_real_unverified_label_still_no_metric(self):
        p = case()
        p["data_kind"] = "real_unverified"
        r = t.evaluate_pair(p)
        self.assertEqual(r["data_kind"], "real_unverified")
        self.assertFalse(r["metric_perturbation_measured"])


if __name__ == "__main__":
    unittest.main()
