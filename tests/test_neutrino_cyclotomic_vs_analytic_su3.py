"""Field-of-definition guard for cyclic SU3 commutator witnesses.

Gotô's 1949 result belongs to compact connected SU3(C).  It does
not automatically inhabit the countable subgroup SU3(Q(zeta3)).
Original source: standard cyclotomic degree formula phi(n).
The witness only obstructs the specified cyclic spectral recipe,
NOT every possible Q(zeta3)-valued commutator factorization.
"""
import unittest
import sympy as s
from test_neutrino_existing_cp_sector_bridge import (
    ROOT_ONE,ROOT_ZETA,ROOT_ZETA2,product)

class CyclotomicVsAnalyticSU3Tests(unittest.TestCase):
    def test_ninth_root_not_in_quadratic_cyclotomic_field(self):
        x=s.Symbol("x")
        f=x**6+x**3+1
        self.assertEqual(s.expand(f),s.cyclotomic_poly(9,x))
        self.assertTrue(s.Poly(f,x,domain=s.QQ).is_irreducible)
        self.assertEqual(s.totient(3),2)
        self.assertEqual(s.totient(9),6)

    def test_cyclic_witness_cannot_normalize_inside_quadratic_field(self):
        # A=T=diag(1,zeta,zeta²), cyclic permutation P.
        # D0=diag(1,1/lambda1,lambda0)=diag(1,zeta²,1).
        d=(ROOT_ONE,ROOT_ZETA2,ROOT_ONE)
        determinant=product(product(d[0],d[1]),d[2])
        self.assertEqual(determinant,ROOT_ZETA2)
        self.assertEqual(product(determinant,ROOT_ZETA),ROOT_ONE)
        # Common phase scalar c must obey c³=zeta; c has order 9.
        x=s.Symbol("x")
        self.assertTrue(s.Poly(s.cyclotomic_poly(9,x),x).is_irreducible)
        self.assertEqual(s.totient(9),6)

    def test_no_universal_commutator_nonexistence_claim(self):
        self.assertEqual(product(ROOT_ZETA,ROOT_ZETA),ROOT_ZETA2)
        # Other factorizations in SU3(Q(zeta)) were not excluded.

if __name__=="__main__":unittest.main()
