"""Original Jarlskog rephasing invariance: exact C3 row-phase steelman.

Model owners: NeutrinoHornedSU3RootExact and
NeutrinoExistingCPSectorLeptonBridgeExact. Verifies that a nontrivial
three-point conjugation orbit is NOT a new physical neutrino observable.
Exact Fraction arithmetic over Q(zeta3), no measured likelihood.
"""
import unittest
from fractions import Fraction as F
from test_neutrino_existing_cp_sector_bridge import (
    pmns, quartet, construct_mass_operators, MASS_SQ,
    ROOT_ONE, ROOT_ZETA, ROOT_ZETA2, ZERO,
    product, add, conjugate
)
ROOTS=(ROOT_ONE,ROOT_ZETA,ROOT_ZETA2)

def phased(U):
    return tuple(tuple(product(ROOTS[a],U[a][i]) for i in range(3))
                 for a in range(3))
def sumq(xs):
    y=ZERO
    for x in xs:y=add(y,x)
    return y
def mm(A,B):
    return tuple(tuple(sumq(product(A[i][k],B[k][j]) for k in range(3))
                       for j in range(3)) for i in range(3))
def adj(A):
    return tuple(tuple(conjugate(A[j][i]) for j in range(3))
                 for i in range(3))
def qnorm(x):
    return product(x,conjugate(x))
def c3conj(A):
    return tuple(tuple(product(product(ROOTS[a],A[a][b]),
                               conjugate(ROOTS[b])) for b in range(3))
                 for a in range(3))
def averaged(U):
    w=tuple(tuple(qnorm(U[a][i])[0] for i in range(3))
            for a in range(3))
    return tuple(tuple(sum(w[a][i]*w[b][i] for i in range(3))
                       for b in range(3)) for a in range(3))
def amp(U,weights,a,b):
    return sumq(product(product(U[b][i],conjugate(U[a][i])),weights[i])
                for i in range(3))

class HornC3RephasingNoGo(unittest.TestCase):
    def test_nontrivial_matrix_orbit(self):
        U=pmns()
        self.assertNotEqual(phased(U),U)
        self.assertEqual(phased(phased(phased(U))),U)

    def test_exact_born_and_astro_average_invariance(self):
        U=pmns();V=phased(U)
        for a in range(3):
            for i in range(3):
                self.assertEqual(qnorm(U[a][i]),qnorm(V[a][i]))
        self.assertEqual(averaged(U),averaged(V))

    def test_CP_odd_Jarlskog_is_identical(self):
        U=pmns()
        self.assertNotEqual(quartet(U)[1],F(0))
        self.assertEqual(quartet(phased(U)),quartet(U))
        self.assertEqual(quartet(phased(phased(U))),quartet(U))

    def test_mass_operator_covariant_not_physically_distinct(self):
        U=pmns();V=phased(U)
        charged,H=construct_mass_operators(U)
        chargedV,HV=construct_mass_operators(V)
        self.assertEqual(chargedV,charged)
        self.assertNotEqual(H,HV)
        self.assertEqual(HV,c3conj(H))
        self.assertEqual(mm(adj(V),mm(HV,V)),
            tuple(tuple((MASS_SQ[i],F(0)) if i==j else ZERO
                        for j in range(3)) for i in range(3)))

    def test_all_9_channel_amplitudes_up_to_row_phase(self):
        U=pmns();V=phased(U);weights=ROOTS
        for a in range(3):
            for b in range(3):
                p=amp(U,weights,a,b)
                v=amp(V,weights,a,b)
                self.assertEqual(v,
                    product(product(ROOTS[b],p),conjugate(ROOTS[a])))
                self.assertEqual(qnorm(v),qnorm(p))

    def test_source_flux_identical(self):
        U=pmns();V=phased(U)
        for source in ((F(1,3),F(2,3),F(0)),
                       (F(1),F(0),F(0)),(F(0),F(1),F(0))):
            for b in range(3):
                def rate(M):
                    return sum(source[a]*averaged(M)[a][b]
                               for a in range(3))
                self.assertEqual(rate(U),rate(V))

if __name__=="__main__":
    unittest.main()
