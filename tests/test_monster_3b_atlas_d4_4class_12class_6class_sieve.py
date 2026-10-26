#!/usr/bin/env python3
"""ATLAS 3B / 2B D4 power-class selector regression.

Original sources: ATLAS Monster power-up tables; Norton--Wilson 2002
for 2.Suz central 2B; Barraclough--Wilson 2007 for N(3B) quotient.
The actual ATLAS 2.Suz:2 D4 matrix witness belongs to original repo #1098.
Tests CONDITIONAL source fusion with a specified rotation class, not an
authenticated Monster class word, 6.Suz degree78 receipt or Agda proof.
"""
import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
SPEC=importlib.util.spec_from_file_location(
    "parity",ROOT/"scripts/monster_3b_suzuki_c2_parity_6class_conditional_gate.py"
)
mod=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(mod)

class Monster3BSourceD4ClassSieve(unittest.TestCase):
    def test_source_atlas_exact_intersection(self):
        rows=mod.check()
        self.assertEqual(len(rows["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"]),4)
        self.assertEqual(
            [(x["source_rotation_class"],x["source_z_times_rotation_class"],
              x["source_z_times_halfturn_class"],x["predicted_selected_phase_trace"])
             for x in rows["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"]],
            [("4A","12B","6E",90),("4C","12H","6E",90),
             ("4C","12I","6E",90),("4D","12F","6B",66)])
        self.assertFalse(
           rows["fourB_2A_old_steelman_applies_to_this_actual_2B_source_D4"])
    def test_selected_4d_forces_the_66_branch(self):
        rows=mod.check("4D")
        self.assertEqual(len(rows["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"]),1)
        x=rows["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"][0]
        self.assertEqual((x["source_family"],x["Schroedinger_inversion_lift_trace"],
                          x["predicted_selected_phase_trace"]),("nonfaithful78_C2plus",1,66))
        self.assertFalse(rows["real_selected_6Suz_degree78_character_verified"])
    def test_4a_and_4c_force_the_90_branch(self):
        for cls,n in (("4A",1),("4C",2)):
            rows=mod.check(cls)["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"]
            self.assertEqual(len(rows),n)
            self.assertTrue(all(x["source_family"]=="faithful78" and
                x["Schroedinger_inversion_lift_trace"]==-1 and
                x["predicted_selected_phase_trace"]==90 for x in rows))
    def test_old_4b_is_not_reintroduced(self):
        for cls in ("4B","4Z","2B","12F",""):
            with self.assertRaises(ValueError):mod.check(cls)
        self.assertEqual(set(mod.ATLAS_TWO_B_POWERUPS_4),{"4A","4C","4D"})
    def test_no_actual_class_weld_pretended(self):
        for cls in (None,"4A","4C","4D"):
            r=mod.check(cls)
            self.assertFalse(r["source_rotation_4A_4C_4D_literal_class_selected"])
            self.assertFalse(r["actual_monster_z_product_class_certified_here"])
            self.assertFalse(r["claim_of_selected_78_identity"])
            self.assertFalse(r["GAP_executed"])

if __name__=="__main__":unittest.main()
