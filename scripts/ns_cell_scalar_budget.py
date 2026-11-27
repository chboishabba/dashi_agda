"""Reverse solve the three original ExtendedCertificateData smallness clauses.
DASHI derivation from Alpoge--Buckmaster StatementDefs.lean, ad53419.
Inputs are exact rational bounds; no actual certificate values are supplied.
"""
from fractions import Fraction as Q
import unittest


def q(x):
    if type(x) not in (Q,int):
        raise ValueError('exact rational inputs required')
    return Q(x)


def terms(weight,period_over_twist,form,actuator_over_multiplier,coercive,sup_factor,size,defect):
    w,P,F0,A,C,H,X,D=map(q,(weight,period_over_twist,form,actuator_over_multiplier,coercive,sup_factor,size,defect))
    if min(w,P,C,H)<=0 or min(F0,A,X,D)<0:
        raise ValueError('source positivity guards')
    F=1/w+2*P*F0
    cap=1/(2*C*H)
    second=4*X*X*(F+2*P*A+2*P/C)
    a=4*X*X*F+4*P*X*D+8*P*A*X*X
    b=8*P*H*X*X
    return cap,second,a,b


def choose_sup(*args):
    """For exact supplied scalars, feasible iff both cap margins positive.
    With outward upper bounds this is sufficient only for underlying values.
    """
    cap,second,a,b=terms(*args)
    m2=cap*cap-second
    m3=cap*cap-b*cap-a
    if min(m2,m3)<=0:
        raise ValueError('no strict supBound for supplied envelope')
    eps=min(cap/2,m2/(4*cap),m3/(4*cap))
    u=cap-eps
    if not (0<u<cap and second<=u*u and a+b*u<=u*u):
        raise ValueError('source smallness check failed')
    return u


class BudgetTests(unittest.TestCase):
    def test_exact_positive(self):
        for C in (1,2,7):
            for H in (1,3):
                for X in (0,Q(1,100000),Q(1,10000)):
                    args=(Q(39,50),2,3,Q(1,2),C,H,X,Q(1,100))
                    U=choose_sup(*args)
                    cap,s,a,b=terms(*args)
                    self.assertLess(U,cap)
                    self.assertLessEqual(s,U*U)
                    self.assertLessEqual(a+b*U,U*U)
    def test_strict_failure(self):
        # second equality at cap, so strict first makes it impossible.
        with self.assertRaises(ValueError):choose_sup(1,1,0,0,1,1,Q(1,2),0)
        # Small second holds but defect makes third fail.
        args=(1,1,0,0,1,1,Q(1,100),100)
        cap,s,a,b=terms(*args)
        self.assertLess(s,cap*cap)
        self.assertGreater(a+b*cap,cap*cap)
        with self.assertRaises(ValueError):choose_sup(*args)
        with self.assertRaises(ValueError):choose_sup(0,1,0,0,1,1,0,0)
    def test_source_expansion(self):
        import sympy as S
        w,P,F,A,C,H,X,D,U=S.symbols('w P F A C H X D U',positive=True)
        a=4*X**2*(1/w+2*P*F)+4*P*X*D+8*P*A*X**2
        b=8*P*H*X**2
        self.assertEqual(S.expand(a+b*U-(4*(1/w+2*P*F)*X**2+4*P*X*(D+2*H*X*U+2*A*X))),0)

if __name__=='__main__':unittest.main()
