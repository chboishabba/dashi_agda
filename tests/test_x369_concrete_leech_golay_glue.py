import unittest
from scripts.check_x369_concrete_leech_golay_glue import (
    certificate as leech, membership, from_coordinates, to_coordinates, translate)
from scripts.check_x369_three_e8_leech_common_glue import (
    certificate as glue, geometry, split, stitch)


class ConcreteLeech(unittest.TestCase):
    def test_exact_basis_shell_and_moves(self):
        r=leech(False)
        self.assertEqual(r['integer_basis_determinant'],2**36)
        self.assertEqual(r['normalized_gram_determinant'],1)
        self.assertEqual(r['minimum_shell_count'],196560)
        self.assertTrue(r['rootlessness_norm16_exclusion'])
        self.assertIsNone(membership((4,)+(0,)*23))
        a=tuple(range(-12,12));x=from_coordinates(a)
        self.assertEqual(to_coordinates(x),a)
        self.assertEqual(translate(x,tuple(-v for v in x)),(0,)*24)

    def test_distinct_glues_common_lattice(self):
        r=glue(False)
        self.assertEqual(r['common_integer_determinant'],2**48)
        self.assertTrue(r['all_720_three_e8_roots_excluded_from_leech'])
        for side,row in r['glue_sides'].items():
            self.assertEqual(row['index'],4096)
            self.assertEqual(row['smith_factors'],[1]*12+[2]*12)
            _,_,_,sides=geometry()
            h=sides[side][2]
            c=tuple(range(-12,12));q=tuple(int(h[i,i])-1 for i in range(24))
            self.assertEqual(split(stitch(c,q,side),side),(c,q))


if __name__=='__main__':
    unittest.main()
