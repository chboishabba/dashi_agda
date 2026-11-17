#!/usr/bin/env python3
"""Focused linear-flag family 16-map check; finite chart only."""
import sys
import unittest
from pathlib import Path
from collections import Counter

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"scripts"))
import monster3b_mixed8_linear_flag_family as fam
import monster3b_mixed8_ordered_E3_pointed729_bidi as codec


class FlagFamily(unittest.TestCase):
    def test_original_lex_chart_is_among_16(self):
        # q(a,b)=a and kernel chart psi(0,b)=b.
        f=fam.flag_map(1,0,1)
        self.assertEqual(f,tuple(codec.encode_outer(*p)[0] for p in fam.X))
        self.assertEqual(Counter(f),{y:10 for y in codec.Y})

    def test_entire_family_and_no_promotion(self):
        receipt=fam.verify()
        self.assertEqual(receipt["distinct_D4_equivariant_balanced_maps"],16)
        self.assertEqual(receipt["source_centralizer_orbits_on_flag_family"],1)
        self.assertEqual(receipt["source_centralizer_stabilizer_order"],3)
        self.assertFalse(receipt["actual_Monster_normalizer_verified"])
        self.assertFalse(receipt["canonical_full_source_invariant_chart"])
        self.assertFalse(receipt["Agda_kernel_verified"])


if __name__=="__main__":
    unittest.main()
