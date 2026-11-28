"""Actual lattice discriminant, mod-2 geometry and central lift contracts."""
import unittest
from scripts.check_x369_leech_discriminant_central_weld import (
    certificate, discriminant_stitch, discriminant_split, lattice_mod2_reopen,
    lattice_mod2_split, split_q, central_mul, lift, action_columns)
from scripts.check_x369_concrete_leech_golay_glue import cycle_action


class LeechDiscriminantCentral(unittest.TestCase):
    def test_actual_glue_and_central_extension(self):
        r=certificate()
        self.assertEqual(r['common_discriminant_order'],1<<24)
        self.assertEqual(r['complementary_glue_dimensions'],[12,12])
        self.assertEqual(r['leech_mod2_order'],1<<24)
        self.assertEqual(r['central_extension_order'],1<<25)
        self.assertEqual(r['isotropic_count_including_zero'],8390656)
        self.assertEqual(r['anisotropic_count'],8386560)
        self.assertEqual(r['generator_pair_checks'],13*24*24)
        self.assertFalse(r['original_monster_flm_action_certified'])

    def test_both_retained_coordinate_inverses(self):
        z=tuple(i-12 for i in range(24))
        for x in (0,1,1<<12,4097,0xabcdef,0xffffff):
            p=discriminant_stitch(z,x)
            self.assertEqual(discriminant_split(p),(z,x))
            self.assertEqual((sum(t*t for t in p)/8)%2,split_q(x))
            h=lattice_mod2_reopen(x,z)
            self.assertEqual(lattice_mod2_split(h),(x,z))
        with self.assertRaises(ValueError):discriminant_stitch(z,1<<24)

    def test_central_sign_not_discarded(self):
        a=(4097,0)
        self.assertEqual(central_mul(a,a),(0,1))
        self.assertEqual(central_mul((1,0),(4096,0)),(4097,1))
        self.assertEqual(central_mul((4096,0),(1,0)),(4097,0))
        cols=action_columns(cycle_action)
        for x,y in ((0xabcdef,0x112233),(1,4096),(0xffffff,0x123456)):
            u,v=(x,1),(y,0)
            self.assertEqual(lift(cols,central_mul(u,v)),
                             central_mul(lift(cols,u),lift(cols,v)))


if __name__=='__main__':unittest.main()
