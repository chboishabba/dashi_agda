"""Exact Q(zeta3) SU(3) target for the POSITIVE horned-group representation.

Primary mathematics: Morikuni Gotô, J Math Soc Japan (1949)
DOI 10.2969/jmsj/00130270 (every element of SU(3) a commutator);
Hatcher, Algebraic Topology, Example 2B.2 (injective free-group tower).

The representation theorem is an abstract group construction, NOT an
identification of the wild complement, a physical PMNS derivation, or
a machine proof of the spectral theorem. The input mixing parameters
and CP phase are selected illustrative fixtures, not model predictions.
"""
import unittest
from fractions import Fraction as F

from test_neutrino_existing_cp_sector_bridge import (
    ZERO, ROOT_ONE, ROOT_ZETA, ROOT_ZETA2, pmns, quartet,
    product, conjugate, add, minus, scale
)


def plus(values):
    s=ZERO
    for value in values:
        s=add(s,value)
    return s


def matmul(A,B):
    return tuple(tuple(plus(product(A[i][k],B[k][j])
                            for k in range(3))
                       for j in range(3)) for i in range(3))


def adjoint(A):
    return tuple(tuple(conjugate(A[j][i]) for j in range(3))
                 for i in range(3))


def eye3():
    return tuple(tuple(ROOT_ONE if i==j else ZERO
                       for j in range(3)) for i in range(3))


def det3(M):
    a,b,c=M[0]
    d,e,f=M[1]
    g,h,i=M[2]
    return add(
        plus((product(a,product(e,i)), product(b,product(f,g)),
              product(c,product(d,h)))),
        minus(plus((product(c,product(e,g)), product(b,product(d,i)),
                    product(a,product(f,h)))))
    )


def matrix_power(A,n):
    acc=eye3()
    for _ in range(n):
        acc=matmul(acc,A)
    return acc


def residual_target():
    U=pmns(ROOT_ZETA)
    # Same S1=2 |first neutrino column><first neutrino column| - I.
    S=tuple(tuple(
        add(scale(F(2),product(U[i][0],conjugate(U[j][0]))),
            minus(ROOT_ONE if i==j else ZERO))
        for j in range(3)) for i in range(3))
    diagonal=(ROOT_ONE,ROOT_ZETA,ROOT_ZETA2)
    A=tuple(tuple(product(diagonal[i],S[i][j])
                  for j in range(3)) for i in range(3))
    return U,S,A


class HornedSU3PositiveTargetTests(unittest.TestCase):
    def test_actual_cp_nonzero_leptonic_mixer(self):
        U,_,_=residual_target()
        self.assertEqual(matmul(U,adjoint(U)),eye3())
        self.assertEqual(matmul(adjoint(U),U),eye3())
        self.assertEqual(
            quartet(U)[1],
            F(9859116742272000,292590225473523169)
        )

    def test_selected_neutral_residual_is_special_unitary(self):
        _,S,_=residual_target()
        self.assertEqual(S,adjoint(S))
        self.assertEqual(matmul(S,S),eye3())
        self.assertEqual(det3(S),ROOT_ONE)

    def test_charged_twist_is_cyclic_order_three(self):
        T=tuple(tuple(
            (ROOT_ONE,ROOT_ZETA,ROOT_ZETA2)[i] if i==j else ZERO
            for j in range(3)) for i in range(3))
        self.assertEqual(matmul(T,adjoint(T)),eye3())
        self.assertEqual(matrix_power(T,3),eye3())
        self.assertEqual(det3(T),ROOT_ONE)
        self.assertNotEqual(T,eye3())

    def test_exact_cp_residual_target_is_in_SU3(self):
        _,_,A=residual_target()
        self.assertEqual(matmul(A,adjoint(A)),eye3())
        self.assertEqual(matmul(adjoint(A),A),eye3())
        self.assertEqual(det3(A),ROOT_ONE)

    def test_same_root_is_infinite_order_by_external_trace_theorem(self):
        _,_,A=residual_target()
        trace=plus(A[i][i] for i in range(3))
        relative_trace=2*trace[0]-trace[1]
        self.assertEqual(relative_trace,F(442358853598,216225930001))
        self.assertTrue(2<relative_trace<3)
        # Standard algebraic-number theorem applies: finite-order
        # matrices have integral relative Galois trace. This file
        # calculates the nonintegrality, not a proof of that theorem.
        self.assertNotEqual(relative_trace.denominator,1)
        self.assertNotEqual(matrix_power(A,5),eye3())

    def test_previous_exact_fifth_power_witness_matches(self):
        _,_,A=residual_target()
        v=matrix_power(A,5)[0][0]
        self.assertEqual(v[0],
            F(64617593685528773022494665450634455935626525583170223342274209281039,
              236441034989226881781955824279450550827785137929884652463470640062961))
        self.assertEqual(v[1],
            -F(37652869638564470030709578649147690575544358178427234909789542400,
               281142728881363711988056865968431094920077452948733237174162473321))

    def test_three_sector_inner_equivariance(self):
        _,_,A=residual_target()
        T=tuple(tuple(
            (ROOT_ONE,ROOT_ZETA,ROOT_ZETA2)[i] if i==j else ZERO
            for j in range(3)) for i in range(3))
        def conjT(x):
            return matmul(matmul(T,x),adjoint(T))
        first,second,third=A,conjT(A),conjT(conjT(A))
        self.assertNotEqual(first,second)
        # Real and zeta coordinate witness: C3 rotation actually
        # moves the selected CP residual, not just Ad_T³=identity.
        delta=add(second[0][1],minus(first[0][1]))
        self.assertEqual(delta[0],F(7429123333440,6270551970029))
        self.assertEqual(delta[1],F(2394922626720,6270551970029))
        self.assertEqual(conjT(first),second)
        self.assertEqual(conjT(second),third)
        self.assertEqual(conjT(third),first)
        # This checks the actual cyclic sector equivariance.
        self.assertEqual(conjT(conjT(conjT(A))),A)
        # A group automorphism preserves commutators.
        def bracket(x,y):
            return matmul(matmul(matmul(x,y),adjoint(x)),adjoint(y))
        U,S,_=residual_target()
        self.assertEqual(conjT(bracket(S,T)),
                         bracket(conjT(S),conjT(T)))


if __name__=="__main__":
    unittest.main()
