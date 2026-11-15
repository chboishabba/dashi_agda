"""Cross-PR order-vs-quotient compatibility test, 2026-10-24.

Source PR #1244: abstract Hatcher three-sector horned group G has
an infinite-order meridian m and a surjection q:G -> A5^3 with
the SELECTED corrected order-five A5 image q(m).
Source PR #1247: the CP-nonzero same-lepton example produces
T=diag(1,zeta,zeta2), S1=2|u1><u1|-I, and TS1 infinite-order.

Important: no automatic representation of the horned exterior
group G, no geometric pi1 isomorphism, and no lepton-VOA/Monster
identification is asserted.  Merely sharing 'infinite order'
does not give an intertwiner.
"""
import unittest
from fractions import Fraction as F

from test_neutrino_existing_cp_sector_bridge import (
    pmns, ROOT_ONE, ROOT_ZETA, ROOT_ZETA2, ZERO,
    product, conjugate, add, minus, scale
)

HORN_CORRECTED_ROOT_FIVE=(2,0,3,4,1)
HORN_EARLIER_UNCONSTRAINED_ROOT_THREE=(2,1,3,0,4)

def compose(a,b):
    return tuple(a[b[i]] for i in range(5))

def permutation_order(p):
    q=tuple(range(5))
    for i in range(1,61):
        q=compose(q,p)
        if q==tuple(range(5)):
            return i
    raise AssertionError("not an A5 finite order")

def mm(A,B):
    ans=[]
    for i in range(3):
        row=[]
        for j in range(3):
            z=ZERO
            for k in range(3):
                z=add(z,product(A[i][k],B[k][j]))
            row.append(z)
        ans.append(tuple(row))
    return tuple(ans)

def ident():
    return tuple(tuple(ROOT_ONE if i==j else ZERO
                       for j in range(3)) for i in range(3))

def matpower(M,n):
    out=ident()
    for i in range(n):
        out=mm(out,M)
    return out

def selected_TS():
    U=pmns(ROOT_ZETA)
    S=tuple(tuple(
        add(scale(F(2),product(U[i][0],conjugate(U[j][0]))),
            minus(ROOT_ONE if i==j else ZERO))
        for j in range(3)) for i in range(3))
    phases=(ROOT_ONE,ROOT_ZETA,ROOT_ZETA2)
    return tuple(tuple(product(phases[i],S[i][j])
                       for j in range(3)) for i in range(3))

class HornedFiniteActorNeutrinoTests(unittest.TestCase):
    def test_selected_root_orders_are_distinct(self):
        self.assertEqual(permutation_order(HORN_EARLIER_UNCONSTRAINED_ROOT_THREE),3)
        self.assertEqual(permutation_order(HORN_CORRECTED_ROOT_FIVE),5)
        self.assertNotEqual(HORN_EARLIER_UNCONSTRAINED_ROOT_THREE,
                            HORN_CORRECTED_ROOT_FIVE)
    
    def test_selected_finite_quotient_meridian_has_fifth_identity(self):
        p=HORN_CORRECTED_ROOT_FIVE
        q=tuple(range(5))
        for _ in range(5):
            q=compose(q,p)
        self.assertEqual(q,tuple(range(5)))
        self.assertNotEqual(p,tuple(range(5)))

    def test_selected_CP_nonzero_TS_has_nontrivial_fifth_power_exactly(self):
        M=selected_TS()
        fifth=matpower(M,5)
        self.assertNotEqual(fifth,ident())
        self.assertNotEqual(fifth[0][0],ROOT_ONE)
        self.assertEqual(
            fifth[0][0][0],
            F(64617593685528773022494665450634455935626525583170223342274209281039,
              236441034989226881781955824279450550827785137929884652463470640062961)
        )
        self.assertEqual(
            fifth[0][0][1],
            -F(37652869638564470030709578649147690575544358178427234909789542400,
               281142728881363711988056865968431094920077452948733237174162473321)
        )

    def test_no_homomorphism_from_selected_A5_actor_sends_root_to_TS(self):
        # If a representation rho of A5^3 sent selected q(m) to TS,
        # rho(q(m)^5)=rho(1)=I but rho(q(m))^5=(TS)^5 != I.
        # This test checks both inputs; the Agda theorem formalizes the
        # generic incompatibility under homomorphism laws.
        self.assertEqual(permutation_order(HORN_CORRECTED_ROOT_FIVE),5)
        self.assertNotEqual(matpower(selected_TS(),5),ident())


if __name__=="__main__":
    unittest.main()
