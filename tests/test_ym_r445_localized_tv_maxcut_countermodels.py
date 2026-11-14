"""Independent unit tests for the seven F19/P0/R445 logical gates.

These are exact rational tests of proposed deductions, not Wilson estimates
or Agda golden checks. Run from repository root:
python3 -m unittest discover -s tests -p 'test_ym_r445_localized_tv_maxcut_countermodels.py' -v
"""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts" / "check_ym_r445_localized_tv_maxcut_countermodels.py"
SPEC = importlib.util.spec_from_file_location("ym_r445_logical_gates", SOURCE)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC is not None and SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class R445LocalizedTVGates(unittest.TestCase):

    def test_exterior_only_weight_changes_correlated_interior(self):
        r = MODULE.external_only_countermodel()
        self.assertEqual(r["TV_X"], "1/8")
        self.assertEqual(r["outside_interacting_activity_touching_X"], 0)

    def test_rare_reference_bad_event_not_small_effective_tv(self):
        r = MODULE.bad_region_reweighting()
        self.assertEqual(r["P_bad_N1000"], "1/2")

    def test_correct_finite_conditional_mixture_bound(self):
        r = MODULE.conditional_mixture_tv()
        self.assertEqual(r["two_site_positive_joint_pairs"], 6561)

    def test_zero_comparison_does_not_make_scale_cauchy(self):
        r = MODULE.noncauchy_zero_tv_comparison()
        self.assertEqual(r["successive_original_measure_TV"], 1)

    def test_zero_tv_does_not_force_clustering(self):
        r = MODULE.nonclustering_zero_tv_comparison()
        self.assertEqual(r["all_separation_covariance"], "1/4")

    def test_positive_probability_does_not_imply_OS_RP(self):
        r = MODULE.no_OS_from_probability_alone()
        self.assertEqual(r["OS_reflection_Gram"], "-1")

    def test_fixed_step_ratio_does_not_make_harmonic_summable(self):
        r = MODULE.fixed_ratio_and_harmonic()
        self.assertEqual(r["single_step_sq"], "1/16")
        self.assertEqual(r["invalid_k2_iterated_sq"], "1/256")
        self.assertEqual(r["blocks_verified"], 10)

    def test_no_clay_endpoint_promoted(self):
        r = MODULE.check()
        self.assertTrue(r["result"] == "PASS")
        self.assertFalse(r["physical_original_Wilson_R445_Dk_proved"])
        self.assertFalse(r["E1_D1_D2_proved"])
        self.assertFalse(r["agda_kernel_checked"])


if __name__ == "__main__":
    unittest.main()
