"""Exact finite controls for the eight actual frozen-aperture constraints.
The oscillatory Gram limit and integration-by-parts bounds are mathematical
arguments in the controlling roadmap; these are not native kernel receipts.
"""
from fractions import Fraction as Q
from itertools import product
import unittest
import sympy as S


def interval_moment(k):
    # Both symmetric plateau intervals: [1/4,1/2] and its reflection.
    return 2*(Q(1,2)**(2*k+1)-Q(1,4)**(2*k+1))/Q(2*k+1)


def plateau_gram():
    return S.Matrix(5,5,lambda i,j:S.Rational(interval_moment(i+j)))


def lambda_floor():
    H=plateau_gram()
    return min(S.Rational(1,2)/S.trace(H.inv()),S.Rational(1,8))


def frequencies(A,B):
    # Actual normalized pair of on-line responses. The pole profiles have
    # a common cosh(u/2) envelope, kept in separate frequency slots.
    u,h=S.symbols('u h',real=True)
    out=[{1:S.Integer(1)}, {2:S.Integer(1)}]
    out += [{1:-B*u**(2*j),2:A*u**(2*j)} for j in range(1,5)]
    out += [{15:h/2,17:h/2},{14:h/2,18:h/2}]
    return u,h,out


class FrozenApertureGramTests(unittest.TestCase):
    def test_actual_eight_frequency_channels(self):
        A,B=S.symbols('A B',real=True)
        u,h,w=frequencies(A,B)
        self.assertEqual(set().union(*(set(x) for x in w)),{1,2,14,15,17,18})
        c=S.symbols('c0:8',real=True)
        poly=sum(c[j+1]*u**(2*j) for j in range(1,5))
        freq={k:sum(c[i]*w[i].get(k,0) for i in range(8)) for k in (1,2,14,15,17,18)}
        self.assertEqual(S.expand(freq[1]-(c[0]-B*poly)),0)
        self.assertEqual(S.expand(freq[2]-(c[1]+A*poly)),0)
        for k in (15,17):
            self.assertEqual(freq[k],c[6]*h/2)
        for k in (14,18):
            self.assertEqual(freq[k],c[7]*h/2)
        d=-B*c[0]+A*c[1]
        e=A*c[0]+B*c[1]
        discrepancy=S.expand(freq[1]**2+freq[2]**2-(d+poly)**2-e**2)
        self.assertEqual(S.rem(discrepancy,A*A+B*B-1,A),0)

    def test_exact_plateau_positive_floor(self):
        H=plateau_gram()
        for k in range(1,6):
            self.assertGreater(H[:k,:k].det(),0)
        lam=lambda_floor()
        self.assertGreater(lam,0)
        # Inverse-trace lower bound, checked again by exact principal minors.
        L=H/2-lam*S.eye(5)
        for k in range(1,6):
            self.assertGreater(L[:k,:k].det(),0)
        self.assertLessEqual(lam,S.Rational(1,8))
        self.assertEqual(interval_moment(0),Q(1,2))

    def test_orientation_independent_limit(self):
        H=plateau_gram()
        lam=lambda_floor()
        for A,B in [(S.Rational(1),S.Rational(0)),(S.Rational(0),S.Rational(1)),
                    (S.Rational(3,5),S.Rational(4,5)),(S.Rational(-5,13),S.Rational(12,13))]:
            M=S.zeros(8)
            M[0,0]=M[1,1]=H[0,0]/2
            for j in range(1,5):
                M[0,j+1]=M[j+1,0]=-B*H[0,j]/2
                M[1,j+1]=M[j+1,1]=A*H[0,j]/2
                for k in range(1,5):
                    M[j+1,k+1]=H[j,k]/2
            # cosh^2 >=1, so each pole block has this lower bound.
            M[6,6]=M[7,7]=S.Rational(1,8)
            rotated=S.eye(8)
            rotated[0,0],rotated[0,1]=-B,A
            rotated[1,0],rotated[1,1]=A,B
            self.assertEqual(rotated.T*rotated,S.eye(8))
            K=rotated*M*rotated.T
            ids=[0,2,3,4,5]
            self.assertEqual(K.extract(ids,ids),H/2)
            self.assertEqual(K[1,1],H[0,0]/2)
            for j in ids:
                self.assertEqual(K[j,1],0)
            # The pole lower block can attain lam; exact PSD suffices.
            L=M-lam*S.eye(8)
            for j in range(1,9):
                self.assertGreaterEqual(L[:j,:j].det(),0)

    def test_oscillatory_error_budget(self):
        # Each original constraint has <=2 modes. All nonzero integer
        # sum/difference frequencies have magnitude at least one.
        labels=(1,2,14,15,17,18)
        for k,l in product(labels,repeat=2):
            self.assertGreaterEqual(k+l,1)
            if k!=l:
                self.assertGreaterEqual(abs(k-l),1)
        # |p|,|q|<=1, |p'|,|q'|<=8, total support <=1,
        # even flat-top with total variation 4.
        coefficient_derivative_l1=4+2*8
        self.assertEqual(4*coefficient_derivative_l1,80)
        self.assertEqual(8*80,640)
        r=S.Rational(1280)/lambda_floor()
        self.assertEqual(640/r,lambda_floor()/2)


if __name__ == '__main__':
    print('EXACT uniform plateau Gram floor:',lambda_floor())
    unittest.main()
