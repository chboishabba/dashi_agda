#!/usr/bin/env python3
"""Exact matrix SU2 -> two-probe Wilson action sign/normalisation regression.

This test *derives* the normalized traces from rational link quaternions;
the E/R/B/vacuum exponents remain explicitly synthetic fixtures. It is NOT
the physical CMP119 complete-density identification.
"""
from __future__ import annotations
import importlib.util
from pathlib import Path
import unittest

P = Path(__file__).resolve().parent

def load(name, filename):
    spec = importlib.util.spec_from_file_location(name,P/filename)
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

matrix = load("matrix_wilson","grqft_su2_literal_wilson_exact.py")
normal = load("source_wilson","grqft_selected_wilson_normalization_audit.py")
IDENTITY=["1","0","0","0"]

def probe(name, link, coupling):
    m=matrix.evaluate({
        "provenance":{"source_id":"toy-SU2","revision":"regression",
                      "cutoff":"one-plaquette","link_frame":"AB-BC-CD-DA"},
        "inverse_bare_coupling_square":coupling,
        "links":{"AB":link,"BC":IDENTITY,"DC":IDENTITY,"AD":IDENTITY}
    })
    w=normal.q(1)-normal.q(m["real_trace"])/2
    return {"configuration_id":name,
            "plaquette_normalized_real_traces":[str(normal.q(m["real_trace"])/2)],
            "exponent_nonwilson_sectors":{"E":"1/3","R":"-1/3",
                                          "B":"0","vacuum":"0"},
            "selected_total_log_density_exponent":str(-4*normal.q(coupling)*w)}

class ActualMatrixNormalizationTest(unittest.TestCase):
    def test_two_independent_nontrivial_SU2_matrix_probes(self):
        receipt={
            "provenance":{
                "source_identifier":"toy-SU2","source_revision":"regression",
                "source_locator":"test-only-not-CMP119",
                "action_identifier":"toy-bare-standard-Wilson",
                "coupling_identifier":"toy-inverse-square",
                "cutoff":"one-plaquette",
                "plaquette_basis":"Wplus=sum(1-ReTrU/2)",
                "trace_convention":"actual-SU2-quaternion-matrix",
                "coefficient_origin":"4-times-supplied-inverse-square"
            },
            "bare_coefficient_convention":"standard_SU2_four_inverse_square",
            "g_squared":"1/2",
            "inverse_g_squared":"2",
            "selected_exponent_sign":"log_density=-action",
            "configurations":[
                probe("first",["0","1","0","0"],"2"),
                probe("second",["3/5","4/5","0","0"],"2")
            ]
        }
        result=normal.audit(receipt)
        self.assertEqual(result["recovered_multi_probe_coefficient"],"-8")
        self.assertEqual(result["probe_count"],2)
        self.assertFalse(result["physical_SU2_matrix_rows_proved"])
        self.assertFalse(result["published_cmp119_source_identification_proved"])

    def test_matrix_link_not_unit_SU2_is_rejected(self):
        with self.assertRaisesRegex(ValueError,"norm exactly one"):
            probe("bad",["1","1","0","0"],"2")

if __name__=="__main__":
    unittest.main()
