#!/usr/bin/env python3
"""Tests of an actual rational SU2 matrix Wilson plaquette, not CMP119."""
from __future__ import annotations
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "wilson", Path(__file__).resolve().parent /
    "grqft_su2_literal_wilson_exact.py")
assert spec and spec.loader
W = importlib.util.module_from_spec(spec)
spec.loader.exec_module(W)

ONE = ["1", "0", "0", "0"]
I = ["0", "1", "0", "0"]
J = ["0", "0", "1", "0"]
K = ["0", "0", "0", "1"]
def source():
    return {
        "provenance":{"source_id":"test-only-SU2","revision":"toy",
                      "cutoff":"one-plaquette","link_frame":"oriented-square"},
        "inverse_bare_coupling_square":"3/2",
        "links":{"AB":I,"BC":ONE,"DC":ONE,"AD":ONE}
    }

class WilsonMatrixTest(unittest.TestCase):
    def test_actual_matrix_holonomy_and_factor_four(self):
        d=W.evaluate(source())
        self.assertEqual(d["holonomy"], ["0","1","0","0"])
        self.assertEqual(d["cost_1_minus_half_trace"], "1")
        self.assertEqual(d["beta_bare_SU2"], "6")
        self.assertEqual(d["bare_wilson_action"], "6")
        self.assertTrue(d["same_action_orientation"])
        self.assertFalse(d["physical_CMP119_effective_action_identified"])

    def test_rational_SU2_gauge_transformation_keeps_real_trace(self):
        s=source()
        s["vertex_gauge"]={"A":I,"B":J,"C":K,"D":ONE}
        d=W.evaluate(s)
        self.assertTrue(d["gauge_trace_invariant"])
        self.assertEqual(d["gauge_transformed_real_trace"],"0")

    def test_identity_plaquette_action_vanishes(self):
        s=source()
        s["links"]={k:ONE for k in ("AB","BC","DC","AD")}
        d=W.evaluate(s)
        self.assertEqual(d["cost_1_minus_half_trace"],"0")
        self.assertEqual(d["bare_wilson_action"],"0")

    def test_unit_norm_is_required(self):
        s=source()
        s["links"]["AB"]=["1","1","0","0"]
        with self.assertRaisesRegex(ValueError,"norm exactly one"):
            W.evaluate(s)

    def test_rational_nontrivial_link(self):
        s=source()
        s["links"]["AB"]=["3/5","4/5","0","0"]
        d=W.evaluate(s)
        self.assertEqual(d["cost_1_minus_half_trace"],"2/5")
        self.assertEqual(d["bare_wilson_action"],"12/5")

if __name__=="__main__":
    unittest.main()
