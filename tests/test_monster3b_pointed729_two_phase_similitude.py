#!/usr/bin/env python3
"""Dual-phase Monster3B SOURCE-TYPE model regression; no actual source promotion."""
import sys, unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_pointed729_two_phase_similitude as model

class DualPhaseSourceType(unittest.TestCase):
    def test_complete_generator_receipt(self):
        r=model.check()
        self.assertEqual(r["dimension"],1458)
        self.assertEqual(r["check_total"],104976)
        self.assertEqual(r["nonidentity_centre_character"],-729)
        self.assertEqual(r["source_type_D4_character_traces"],dict(r=2,r2=2,m=0))
        self.assertEqual(r["D4_irrep_multiplicities"],dict(
            A1=183,A2=183,B1=182,B2=182,E=364))
        self.assertEqual(r["preserving_nine_translations"],9)
        self.assertEqual(r["moving_nine_translations"],720)
        self.assertTrue(r["mirror_exchanges_phases"])
        for x in ("actual_ATLAS_generator_words_selected",
                  "genuine_6Suz78_family_selected","source_Monster_Hom_proved",
                  "IIT_observable_transport_proved","Agda_kernel_checked"):
            self.assertIs(r[x],False)

if __name__=="__main__":
    unittest.main()
