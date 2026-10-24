"""Exact C3-cyclotomic CP-odd same-lepton mass-operator regression.

ORIGINAL THEORY:
  C. Jarlskog, PRL 55 (1985) 1039; PRD 35 (1987) 1685
  PDG 2025 neutrino mixing review; NuFIT 6.1 (2025).
EXISTING DASHI DONORS:
  C3CyclotomicAmplitudeAlgebraExact, JarlskogDiagnosticAnalysis,
  CPPhaseStructuralOriginReceipt, HeckeCharacterPhaseReceipt,
  Y13ComplexEntryReceipt, CKMGateAbRetirementReceipt.
NEW CODE:
  NeutrinoExistingCPSectorLeptonBridgeExact.agda.

This mathematically *constructs* an exact nonzero leptonic CP-odd invariant
at an ILLUSTRATIVE delta_CP = +120 deg, with measured-angle-inspired
rational pair inputs chosen post hoc.  It does not predict observed
leptonic CP violation; CKM phase diagnostics are not PMNS mass data.
"""
from fractions import Fraction as F
from itertools import product
import math
import unittest

ROOT_ONE=(F(1),F(0))
ROOT_ZETA=(F(0),F(1))
ROOT_ZETA2=(F(-1),F(-1))
ZERO=(F(0),F(0))
S12,C12=F(161,289),F(240,289)
S13,C13=F(240,1609),F(1591,1609)
S23,C23=F(20,29),F(21,29)
MASS_SQ=(F(0),F(7537),F(251100))
CHARGED_MASS_SQ=(F(1),F(4),F(9))
EXPECTED_CP_COEFF=F(9859116742272000,292590225473523169)
EXPECTED_TRACE_CUBE_COEFF=F(
    3272103619391689547963065344000000,
    292590225473523169
)
EXPECTED_TRACE_CUBE_RATIO=331886081170152000

def add(x,y):
    return x[0]+y[0],x[1]+y[1]

def minus(x):
    return -x[0],-x[1]

def scale(q,x):
    return q*x[0],q*x[1]

def product(x,y):
    a,b=x;c,d=y
    return a*c-b*d,a*d+b*c-b*d

def conjugate(x):
    a,b=x
    return a-b,-b

def scalar(q):
    return (F(q),F(0))

def sumv(values):
    out=ZERO
    for v in values:
        out=add(out,v)
    return out

def matmul(A,B):
    return tuple(tuple(sumv(product(A[i][k],B[k][j])
                            for k in range(3))
                       for j in range(3))
                 for i in range(3))

def dagger(A):
    return tuple(tuple(conjugate(A[j][i]) for j in range(3))
                 for i in range(3))

def diagonal(values):
    return tuple(tuple(scalar(values[i]) if i==j else ZERO
                       for j in range(3))
                 for i in range(3))

def pmns(delta_root=ROOT_ZETA):
    # exp(+i delta)=root; its conjugate appears in U_e3.
    p=delta_root
    return (
        (scalar(C12*C13),scalar(S12*C13),scale(S13,conjugate(p))),
        (add(scalar(-S12*C23),scale(-C12*S23*S13,p)),
         add(scalar(C12*C23),scale(-S12*S23*S13,p)),scalar(S23*C13)),
        (add(scalar(S12*S23),scale(-C12*C23*S13,p)),
         add(scalar(-C12*S23),scale(-S12*C23*S13,p)),scalar(C23*C13)),
    )

def quartet(U):
    return product(
        product(
            product(U[0][0],U[1][1]),conjugate(U[0][1])),
        conjugate(U[1][0])
    )

def construct_mass_operators(U):
    charged=diagonal(CHARGED_MASS_SQ)
    neutral=matmul(matmul(U,diagonal(MASS_SQ)),dagger(U))
    return charged,neutral

def commutator(A,B):
    AB=matmul(A,B)
    BA=matmul(B,A)
    return tuple(tuple(add(AB[i][j],minus(BA[i][j]))
                       for j in range(3))
                 for i in range(3))

def trace(A):
    return sumv(A[i][i] for i in range(3))


class ExactLeptonCPTests(unittest.TestCase):
    def test_original_exact_ternary_phases_and_no_fourth_zero(self):
        self.assertEqual(product(ROOT_ZETA,ROOT_ZETA),ROOT_ZETA2)
        self.assertEqual(product(ROOT_ZETA,ROOT_ZETA2),ROOT_ONE)
        self.assertEqual(sumv([ROOT_ONE,ROOT_ZETA,ROOT_ZETA2]),ZERO)
        self.assertNotIn(ZERO,(ROOT_ONE,ROOT_ZETA,ROOT_ZETA2))

    def test_rational_trigonometric_pairs_are_norm_one(self):
        for s,c in ((S12,C12),(S13,C13),(S23,C23)):
            self.assertEqual(s*s+c*c,F(1))

    def test_exact_complex_pmns_unitary_both_sides(self):
        U=pmns()
        self.assertEqual(matmul(U,dagger(U)),diagonal([1]*3))
        self.assertEqual(matmul(dagger(U),U),diagonal([1]*3))

    def test_cp_odd_leptonic_quartet_is_nonzero_exact(self):
        q=quartet(pmns())
        self.assertEqual(q[1],EXPECTED_CP_COEFF)
        self.assertNotEqual(q,conjugate(q))
        self.assertGreater(q[1],0)
        self.assertAlmostEqual(
            float(q[1])*math.sqrt(3)/2,0.029181581660378,places=13
        )

    def test_cp_conjugation_reverses_odd_coefficient(self):
        q=quartet(pmns(ROOT_ZETA))
        qc=quartet(pmns(ROOT_ZETA2))
        self.assertEqual(qc,conjugate(q))
        self.assertEqual(qc[1],-EXPECTED_CP_COEFF)

    def test_same_lepton_space_neutrino_mass_operator_eigenvectors(self):
        U=pmns()
        charged,neutral=construct_mass_operators(U)
        self.assertEqual(neutral,dagger(neutral))
        self.assertEqual(
            matmul(matmul(dagger(U),neutral),U), diagonal(MASS_SQ)
        )
        self.assertNotEqual(matmul(charged,neutral),matmul(neutral,charged))

    def test_complex_hamiltonian_cp_odd_commutator_invariant(self):
        # Historical Jarlskog theorem, here calculated independently in
        # Q(zeta): Tr([H_charged,H_neutral]^3) proportional to quartet J.
        U=pmns()
        charged,neutral=construct_mass_operators(U)
        K=commutator(charged,neutral)
        cubic_trace=trace(matmul(matmul(K,K),K))
        self.assertEqual(cubic_trace[0],cubic_trace[1]/2)
        self.assertEqual(cubic_trace[1],EXPECTED_TRACE_CUBE_COEFF)
        self.assertEqual(cubic_trace[1]/quartet(U)[1],
                         EXPECTED_TRACE_CUBE_RATIO)
        self.assertNotEqual(cubic_trace,ZERO)
        self.assertEqual(cubic_trace,minus(conjugate(cubic_trace)))
        mass_product=(MASS_SQ[0]-MASS_SQ[1]) * (
            MASS_SQ[1]-MASS_SQ[2])*(MASS_SQ[2]-MASS_SQ[0])
        charged_product=(
            (CHARGED_MASS_SQ[0]-CHARGED_MASS_SQ[1])*
            (CHARGED_MASS_SQ[1]-CHARGED_MASS_SQ[2])*
            (CHARGED_MASS_SQ[2]-CHARGED_MASS_SQ[0])
        )
        self.assertEqual(
            cubic_trace[1],6*mass_product*charged_product*quartet(U)[1]
        )

    def test_nonzero_cp_does_not_make_selected_C3_residual_group_finite(self):
        # T=diag(1,zeta,zeta²); S1=2|u1><u1|-I.
        # tr(T S1)=a+b*zeta, with a,b rational because delta=120deg.
        # Its rational field trace is 2*a-b, not an integer.
        # By the classical algebraic-integer theorem TS1 has infinite
        # order. That theorem is not newly proved here.
        U=pmns(ROOT_ZETA)
        self.assertNotEqual(quartet(U)[1],F(0))
        def field_norm(z):
            a,b=z
            return a*a-a*b+b*b
        diagonal=[2*field_norm(U[a][0])-1 for a in range(3)]
        a=diagonal[0]-diagonal[2]
        b=diagonal[1]-diagonal[2]
        q=2*a-b
        self.assertEqual(q,F(442358853598,216225930001))
        self.assertEqual(q,F(372023795875918,181846007130841))
        self.assertEqual(q,6*field_norm(U[0][0])-2)
        self.assertTrue(F(2)<q<F(3))
        self.assertNotEqual(q.denominator,1)

    def test_cp_conserving_real_branch_has_zero_cp_odd_invariant(self):
        U=pmns(ROOT_ONE)
        self.assertEqual(quartet(U)[1],0)
        charged,neutral=construct_mass_operators(U)
        K=commutator(charged,neutral)
        self.assertEqual(trace(matmul(matmul(K,K),K)),ZERO)

    def test_discrete_c3_cp_is_not_physical_nufit_best_fit(self):
        # The actual chosen phases 120 and 240 degrees are options,
        # not a PMNS-phase prediction from CKM or Monster sectors.
        self.assertNotEqual(120,212)
        self.assertNotEqual(240,212)
        nuFit_delta=math.radians(212)
        Jmax=float(
            S12*C12*S23*C23*C13*C13*S13
        )
        self.assertAlmostEqual(
            Jmax*math.sin(math.radians(120)),0.029181581660378,places=13
        )
        self.assertLess(Jmax*math.sin(nuFit_delta),0)


if __name__=="__main__":
    unittest.main()
