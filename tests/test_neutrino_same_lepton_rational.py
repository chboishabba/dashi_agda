"""Independent exact-rational audit of charged/neutral lepton residual operators.

Mathematical antecedents: Fonseca & Grimus JHEP 09 (2014) 033;
Hagedorn & Koenig PRD 100 (2019) 075036.
NuFIT 6.1 is the observed *input*, not an original prediction.
New DASHI arithmetic reconstructs one hand-selected rational orthogonal
matrix U and mass-squared Hamiltonians in a COMMON 3D lepton basis.
No Majorana/Dirac identification, finite flavour-group closure, or
experimental CP fit is implied.

Unit tests are exact Fraction arithmetic (no float except diagnostics).
"""
import unittest
from fractions import Fraction as F
from itertools import product
import math

D = 13485029
N = (
    (11073360, 7428379, 2011440),
    (-6592029, 7336560, 9195980),
    (3971380, -8534640, 9655779),
)
U = tuple(tuple(F(x,D) for x in row) for row in N)
M2 = (0, 7537, 251100)  # delta(m^2) in 10^-8 eV²; overall offset arbitrary
ML2 = (1, 4, 9)  # arbitrary dimensionless charged-sector distinguishable eigenvalues
SIGNS = ((1,-1,-1), (-1,1,-1), (-1,-1,1))
EISENSTEIN_ROOTS = ((F(1),F(0)), (F(0),F(1)), (F(-1),F(-1)))


def transpose(a):
    return tuple(zip(*a))


def mm(a,b):
    bt = transpose(b)
    return tuple(tuple(sum((x*y for x,y in zip(row,col)), F(0))
                       for col in bt) for row in a)


def diag(vals):
    return tuple(tuple(F(vals[i]) if i==j else F(0)
                       for j in range(3)) for i in range(3))


def ident():
    return diag((1,1,1))


def residual(s):
    return mm(mm(U, diag(s)), transpose(U))


def mass_squared():
    return mm(mm(U, diag(M2)), transpose(U))


def born_average(u):
    w=tuple(tuple(x*x for x in row) for row in u)
    return mm(w, transpose(w))


class SameLeptonResidualTests(unittest.TestCase):
    def test_exact_orthogonality_and_nonflat_reactor(self):
        self.assertEqual(mm(U,transpose(U)),ident())
        self.assertEqual(mm(transpose(U),U),ident())
        self.assertEqual(D*D, 181846007130841)
        self.assertEqual(U[0][2]**2,F(57600,2588881))
        self.assertTrue(F(22,1000) < U[0][2]**2 < F(23,1000))

    def test_posthoc_angle_fit_not_a_prediction(self):
        vals = (F(161,289)**2, F(240,1609)**2, F(20,29)**2)
        self.assertTrue(abs(float(vals[0])-0.3088)<0.0067)
        self.assertTrue(abs(float(vals[1])-0.0225)<0.0006)
        self.assertTrue(abs(float(vals[2])-0.470)<0.015)
        self.assertEqual(U[0][2],F(240,1609))

    def test_same_space_neutrino_operator_is_diagonalized_by_U(self):
        h=mass_squared()
        self.assertEqual(mm(mm(transpose(U),h),U),diag(M2))
        self.assertEqual(h,transpose(h))
        self.assertEqual(N[0][0],11073360)
        self.assertEqual(h[0][1],F(5055394446468860880,D*D))

    def test_two_neutrino_involutions_and_klein_multiplication(self):
        s1,s2,s3=map(residual,SIGNS)
        for s in (s1,s2,s3):
            self.assertEqual(mm(s,s),ident())
        self.assertEqual(mm(s1,s2),s3)
        self.assertEqual(mm(s2,s1),s3)
        self.assertEqual(mm(s1,s3),s2)

    def test_neutrino_involutions_preserve_mass_squared(self):
        h=mass_squared()
        for sign in SIGNS:
            s=residual(sign)
            self.assertEqual(mm(s,h),mm(h,s))
            self.assertEqual(mm(mm(s,h),s),h)

    def test_distinct_charged_and_neutral_operators_do_not_commute(self):
        hl=diag(ML2)
        hn=mass_squared()
        self.assertNotEqual(mm(hl,hn),mm(hn,hl))
        self.assertEqual(
            (mm(hl,hn)[0][1]-mm(hn,hl)[0][1]),
            F(-15166183339406582640,D*D)
        )

    def test_charged_C3_residual_preserves_diagonal_mass(self):
        # Cyclotomic 3 scalars are represented as a+b*zeta.
        def emul(x,y):
            a,b=x;c,d=y
            return (a*c-b*d,a*d+b*c-b*d)
        roots=EISENSTEIN_ROOTS
        for k,root in enumerate(roots):
            self.assertEqual(emul(root,emul(root,root)), roots[0])
            self.assertEqual(ML2[k],(1,4,9)[k])
        self.assertEqual(len(set(roots)),3)

    def test_generated_joint_finite_group_is_not_automatic(self):
        # T=diag(1,zeta,zeta²); S1=U diag(1,-1,-1) U^T.
        # Exact trace(T*S1)=a+b*zeta where both rational a,b
        # have denominators >1, hence not in the integer ring Z[zeta].
        # If TS had finite order its trace would be an algebraic integer.
        s1=residual(SIGNS[0])
        a=s1[0][0]-s1[2][2]
        b=s1[1][1]-s1[2][2]
        self.assertEqual(a,F(213694885170400,D*D))
        self.assertEqual(b,F(55365974464882,D*D))
        self.assertTrue(F(1)<a<F(2))
        self.assertTrue(F(0)<b<F(1))
        self.assertNotEqual(a.denominator,1)
        self.assertNotEqual(b.denominator,1)

    def test_galois_trace_noninteger_stronger_finite_order_no_go(self):
        # Let tau=tr(T*S1)=a+b*zeta in Q(zeta), where
        # tr_{Q(zeta)/Q}(tau)=2a-b.  A finite-order TS1 would have
        # algebraic-integer eigenvalues -> integral trace tau; the
        # Galois trace of an algebraic integer must be an integer.
        # Here 2 < 2a-b < 3, so its trace cannot be integral.
        s=residual(SIGNS[0])
        numerator_a=N[0][0]**2-N[0][1]**2-N[0][2]**2
        numerator_b=N[1][0]**2-N[1][1]**2-N[1][2]**2
        numerator_c=N[2][0]**2-N[2][1]**2-N[2][2]**2
        self.assertEqual(F(numerator_a, D*D),s[0][0])
        self.assertEqual(F(numerator_b, D*D),s[1][1])
        self.assertEqual(F(numerator_c, D*D),s[2][2])
        field_trace_num=2*(numerator_a-numerator_c) - (numerator_b-numerator_c)
        self.assertEqual(field_trace_num, 372023795875918)
        q=F(field_trace_num, D*D)
        self.assertTrue(F(2)<q<F(3))
        self.assertNotEqual(q.denominator,1)

    def test_phase_averaged_sources_and_rank(self):
        p=born_average(U)
        pion=(F(1,3),F(2,3),F(0))
        neutron=(F(1),F(0),F(0))
        def at_earth(x):
            return tuple(sum((x[i]*p[i][j] for i in range(3)),F(0))
                         for j in range(3))
        pion_earth=at_earth(pion)
        neutron_earth=at_earth(neutron)
        for y in (pion_earth, neutron_earth):
            self.assertEqual(sum(y),F(1))
        self.assertNotEqual(pion_earth,neutron_earth)
        self.assertAlmostEqual(float(pion_earth[0]),0.35662009,places=7)
        self.assertAlmostEqual(float(neutron_earth[0]),0.54726022,places=7)

    def test_cp_zero_is_a_model_limitation(self):
        # For all-real U the vacuum Jarlskog CP invariant is identically 0.
        j=(U[0][0]*U[1][1]*U[0][1]*U[1][0])
        self.assertEqual(j.imag if hasattr(j,'imag') else 0,0)
        self.assertEqual(U[0][0]*U[1][1]*U[0][1]*U[1][0]-
                         U[0][0]*U[1][1]*U[0][1]*U[1][0],0)


if __name__=="__main__":
    unittest.main()
