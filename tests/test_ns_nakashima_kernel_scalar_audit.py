"""Independent scalar audit of Nakashima's stated 2026 quartic temporal kernel.

Original author/source: Ken Nakashima, 'Toward Global Regularity ...',
Part II, published 16 October 2026, https://ken-theory.org/?page_id=25343.
The page reports 48 nonzero ordered paths and grouped coefficients
A_8=2688/5, A_12=0, A_14=-4704/5 (UNVERIFIED path enumeration).
The displayed kernel is a conditional reconstructed coefficient, not
an inequality on full physical Fourier correlations or R735 W2.
"""
import sympy as s


def groups():
    return {8:s.Rational(2688,5),12:s.Integer(0),14:-s.Rational(4704,5)}


def kernel(t,nu):
    return s.simplify(sum((a*(1-s.exp(-rate*nu*t))/(rate*nu)
                           for rate,a in groups().items()),s.Integer(0)))


def test_grouped_viscosity_cancelled_constant_reconstruction():
    t,nu=s.symbols('t nu',positive=True)
    assert sum((a/s.Integer(rate) for rate,a in groups().items()),s.Integer(0))==0
    exact=s.Rational(336,5)/nu*(s.exp(-14*nu*t)-s.exp(-8*nu*t))
    assert s.simplify(kernel(t,nu)-exact)==0
    assert kernel(s.Integer(0),nu)==0


def test_negative_kernel_and_negative_integral_are_scalar_not_work_sign():
    t,nu=s.symbols('t nu',positive=True)
    C=kernel(t,nu)
    assert s.integrate(C,(t,0,s.oo))==-s.Rational(18,5)/nu**2
    for tm,visc in [(s.Rational(1,10),1),(1,2),(2,s.Rational(1,2))]:
        assert s.N(C.subs({t:tm,nu:visc}))<0


def test_complex_correlation_sign_is_not_implied_by_negative_kernel():
    t,nu=s.symbols('t nu',positive=True)
    C=kernel(t,nu)
    # Algebraic independent correlations z=+1,z=-1 have opposite
    # signed work for the same negative scalar kernel. This is NOT
    # a claim either correlation is source-realizable for all t.
    for sign in (1,-1):
        signed=s.integrate(s.re(sign)*C,(t,0,s.oo))
        assert signed==-sign*s.Rational(18,5)/nu**2
