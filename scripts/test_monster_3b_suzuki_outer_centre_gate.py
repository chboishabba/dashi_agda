#!/usr/bin/env python3
"""Regression of the original-source fused-1458 outer-coset receipt gate.

Synthetic minimal JSON rows ONLY. This verifies the validator is fail-closed
against pre-gate receipts or forged booleans, not that GAP/CTblLib executed.
"""
import sys
from pathlib import Path
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from render_monster_3b_suzuki_main_quotient_match import validate

def minimal_prefix():
    return dict(main_table="3^1+12:6.Suz.2",
        six_suz_table="6.Suz",six_suz_outer_table="6.Suz.2",
        mn3b_table="MN3B",six_suz_group_order=2690072985600,
        six_suz_class_count=210,
        six_suz_degree12_positions=[1,2],
        six_suz_degree78_positions=[3,4],
        base_1458_main_position=1,
        base_1458_extraspecial_central_class_position=3,
        base_1458_central_trace=-729)

class Fused1458InvertingCosetGate(unittest.TestCase):
    def test_missing_and_false_fail_before_later_source_fields(self):
        for value in ("missing",False,0,1,"true",None):
            p=minimal_prefix()
            if value!="missing":
                p["base_1458_outer_centre_inverting_trace_zero"]=value
            with self.assertRaisesRegex(ValueError,
                    "base_1458_outer_centre_inverting_trace_zero"):
                validate(p)

    def test_true_passes_this_gate_without_paying_later_gates(self):
        p=minimal_prefix()
        p["base_1458_outer_centre_inverting_trace_zero"]=True
        with self.assertRaises(ValueError) as err:
            validate(p)
        self.assertNotIn("outer_centre_inverting_trace_zero",str(err.exception))
        self.assertIn("qg_to_n3b_kernel",str(err.exception))

if __name__=="__main__":
    unittest.main()
