"""Exact affine SSPRK3 source gate and unobserved history covectors.
SymPy local proof of the finite stage identities; not production convergence.
"""
import sympy as s


def active(amplitudes):
    """No tolerance: even arbitrarily small nonzero source remains active."""
    return any(a != 0 for a in amplitudes)


def check():
    # Independent clock-dependent physical/history blocks, independent source rows.
    # Noncommuting symbols preserve stage order (scalar source coefficients commute).
    I=s.Symbol('I',commutative=False)
    L0,L1,L2,B0,B1,B2,x,g0,g1=s.symbols('L0 L1 L2 B0 B1 B2 x g0 g1',commutative=False)
    h,a0,a1,a2=s.symbols('h a0 a1 a2',real=True)
    def step(x,g):
        A=x+h*(L0*x+a0*B0*g)
        B=s.Rational(3,4)*x+s.Rational(1,4)*(A+h*(L1*A+a1*B1*g))
        return s.Rational(1,3)*x+s.Rational(2,3)*(B+h*(L2*B+a2*B2*g))
    D=s.expand(step(x,g0)-step(x,g1))
    assert s.expand(D-step(0,g0-g1))==0
    assert D.subs({a0:0,a1:0,a2:0})==0
    # All three clocks matter; no endpoint-only gate.
    for a in (a0,a1,a2):
        assert s.expand(D.subs({b:0 for b in (a0,a1,a2) if b!=a}))!=0
    assert not active([0,0,0]) and active([0,0,1e-300])
    # Six-channel history derivative is downstream of physical state only.
    E=s.Matrix(2,2,s.symbols('e:4')); H=s.Matrix(3,2,s.symbols('h:6'))
    M=E.row_join(s.zeros(2,3)).col_join(H.row_join(s.eye(3)))
    p=s.Matrix(s.symbols('p:2')); z=s.zeros(3,1)
    assert M.T*p.col_join(z)==(E.T*p).col_join(z)
    # Observe at any number of time slots, never reintroduce history cotangents.
    O=s.Matrix(s.symbols('o:2')).col_join(z)
    assert (O+M.T*p.col_join(z))[2:]==[0,0,0]
    return dict(exact_groups=8,source_clock_negative_controls=3)


if __name__=='__main__':print(check())
