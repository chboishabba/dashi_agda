import unittest
from scripts.x369_y443_actual_monster_quotient import incidence_check,relators,U,V,BETA,NODES


class Y443Source(unittest.TestCase):
    def test_original_incidence_and_relators(self):
        self.assertEqual(incidence_check(),11)
        r=relators()
        self.assertEqual(len(r),80)
        self.assertEqual(sum(map(len,r)),463)
        self.assertEqual([len(w) for w in r[-2:]],[90,63])
        self.assertEqual(sum(len(w)%2 for w in r),1)

    def test_literal_original_jmd_paths(self):
        self.assertEqual(U,('d3','c3','b3','a','b1','c1','d1','e1'))
        self.assertEqual(BETA,('b2','c2','d2','e2'))
        self.assertEqual(set(U+BETA),set(NODES))
        self.assertEqual(V,U+('e1',)+BETA)

if __name__=='__main__':unittest.main()
