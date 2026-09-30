#!/usr/bin/env python3
"""Finite *actual SU2 matrix* metric-partition-response regression tests.

These are deliberately sparse DISCRETE quadratures, not physical CMP119 Haar.
"""
from __future__ import annotations
import importlib.util
from fractions import Fraction as F
from pathlib import Path
import unittest

spec=importlib.util.spec_from_file_location(
    "source",Path(__file__).with_name("grqft_su2_six_plane_partition_metric_source.py"))
assert spec and spec.loader
source=importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
ONE=["1","0","0","0"]
Q=["0","1","0","0"]
R=["3/5","4/5","0","0"]
ZERO_D={a:"0" for a in "0123"}

def make_fixture(link=Q, vacuum=None):
    planes={p:{"AB":(link if p=="01" else ONE),"BC":ONE,
               "DC":ONE,"AD":ONE} for p in source.PLANES}
    sectors={s:{"action":"0","diagonal_derivative":ZERO_D.copy()}
             for s in source.SECTORS}
    if vacuum is not None:
        # Explicit toy cosmological term S_v = λ sqrt(det g) at g=identity.
        # λ is NOT computed from CMP119 or quantum Yang-Mills.
        lam=F(vacuum)
        sectors["vacuum"]={
            "action":str(lam),
            "diagonal_derivative":{a:str(lam/2) for a in "0123"}
        }
    return {
        "model":"six_plane_euclidean_SU2_discrete_quadrature",
        "provenance":{"source_identifier":"test-only-SU2",
                      "revision":"toy-metric-identity",
                      "cutoff":"one-matrix-six-plaquette",
                      "sector_provenance":"explicit-fixture-not-CMP119"},
        "inverse_bare_coupling_square":"1/4",
        "configurations":[{
            "id":"configuration-1","reference_weight":"1",
            "plaquettes":planes,
            "sectors":sectors,
            "reference_log_derivative":ZERO_D.copy()
        }]
    }

def within(interval,target,tolerance=F(1,10**8)):
    lo,hi=(F(x) for x in interval)
    return lo<=target<=hi and hi-lo<tolerance

class PhysicalMatrixFirstResponseTest(unittest.TestCase):
    def test_actual_six_plane_wilson_action_and_metric_derivative(self):
        out=source.one_point(make_fixture())
        r=out["configuration_rows"][0]
        self.assertEqual(r["six_plaquette_energies"]["01"],"1")
        self.assertEqual(r["wilson_metric_derivative"],
                         {"0":"-1/2","1":"-1/2","2":"1/2","3":"1/2"})
        self.assertEqual(r["complete_action"],"1")
        self.assertEqual(out["bare_beta_SU2"],"1")
        self.assertTrue(out["bare_wilson_only_trace_exactly_zero"])
        self.assertEqual(out["four_diagonal_correlated_trace_interval"],["0","0"])
        self.assertTrue(within(out["D_logZ_interval"]["0"],F(1,2)))
        self.assertTrue(within(out["D_logZ_interval"]["2"],-F(1,2)))
        self.assertFalse(out["renormalized_Lorentzian_stress_identified"])

    def test_selected_vacuum_volume_shift_is_not_derived_quantum_energy(self):
        out=source.one_point(make_fixture(vacuum="1"))
        self.assertEqual(out["configuration_rows"][0]["weighted_action_trace"],"2")
        self.assertTrue(within(
            out["four_diagonal_correlated_trace_interval"],F(-2)))
        self.assertFalse(out["accelerated_expansion_derived"])
        self.assertFalse(out["published_CMP119_measure_constructed"])

    def test_exact_SU2_links_not_assumed_trace(self):
        out=source.one_point(make_fixture(link=R))
        self.assertEqual(out["configuration_rows"][0]["wilson_action"],"2/5")
        self.assertEqual(out["configuration_rows"][0]["six_plaquette_energies"]["01"],"2/5")
        self.assertEqual(out["four_diagonal_correlated_trace_interval"],["0","0"])

    def test_rejects_missing_physical_E_R_B_V_sector(self):
        f=make_fixture()
        del f["configurations"][0]["sectors"]["R"]
        with self.assertRaisesRegex(ValueError,"complete E/R/B/vacuum"):
            source.one_point(f)

    def test_rejects_missing_actual_plane(self):
        f=make_fixture()
        del f["configurations"][0]["plaquettes"]["23"]
        with self.assertRaisesRegex(ValueError,"six actual SU2"):
            source.one_point(f)

    def test_rejects_nonunit_quaternion(self):
        f=make_fixture()
        f["configurations"][0]["plaquettes"]["01"]["AB"]=["1","1","0","0"]
        with self.assertRaisesRegex(ValueError,"norm exactly one"):
            source.one_point(f)

    def test_rejects_reference_score_without_probability_normalization(self):
        f=make_fixture()
        f["configurations"][0]["reference_log_derivative"]["0"]="1"
        with self.assertRaisesRegex(ValueError,"D_h integral 1"):
            source.one_point(f)

    def test_selected_partition_strictly_positive(self):
        out=source.one_point(make_fixture())
        self.assertGreater(F(out["partition_interval"][0]),0)

    def test_exponential_interval_positive_for_negative_action(self):
        lo,hi=source.exp_neg_interval(F(-1))
        self.assertGreater(lo,0)
        self.assertLessEqual(lo,hi)
        self.assertLess(hi-lo,F(1,10**8))

if __name__=="__main__":
    unittest.main()
