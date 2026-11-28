"""Mixed CRT central algebra. Actual Monster adapters require mmgroup."""
import unittest
from scripts.check_x369_mixed_central_monster_source import (
    crt,split6,encode,decode,mixed_mul,mul3,certificate)
from scripts.check_x369_leech_discriminant_central_weld import central_mul


class MixedCentral(unittest.TestCase):
    def test_exact_mixed_pair_law(self):
        r=certificate()
        self.assertEqual(r['one_pair_exhaustive_products'],46656)
        self.assertEqual(r['product_order'],2**25*3**13)
        self.assertEqual(r['centre_order'],6)
        self.assertFalse(r['direct_product_embedded_in_monster'])

    def test_retained_binary_pairs_and_both_centres(self):
        zero=(0,)*6;a=(1,2,0,1,2,0);b=(2,0,1,2,0,1)
        x=(0xabcdef,1);y=(0x123456,0)
        u=(a,b,2);v=(b,a,1)
        self.assertEqual(decode(encode(x,u)),(x,u))
        self.assertEqual(decode(mixed_mul(encode(x,u),encode(y,v))),
                         (central_mul(x,y),mul3(u,v)))
        self.assertEqual(split6(crt(1,2)),(1,2))
        self.assertNotEqual(encode((1<<6,0),(zero,zero,0)),
                            encode((0,0),(zero,zero,0)))
        with self.assertRaises(ValueError):split6(6)


if __name__=='__main__':unittest.main()
