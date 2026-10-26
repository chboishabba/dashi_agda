"""R734 original cube-dyadic critical-energy residence and sharp heat-shear cut.

Original roots: Leray energy identity, Fourier Cauchy interpolation, and
Fujita--Kato critical regularity theory. Repository-specific input: its literal
w(k)=2^ceil(log2 ||k||_infty) multiplier. Exact arithmetic/SymPy receipts do
NOT constitute a kernel proof or an unrestricted NSE continuation theorem.
"""
from fractions import Fraction as F
from itertools import product
import sympy as S


def weight(m):
    radius=max(map(abs,m))
    if radius<1:
        raise ValueError("the zero mode is excluded")
    return 1 << (radius-1).bit_length()


def test_all_cube_modes_weighted_critical_interpolation():
    for k in product(range(-8,9), repeat=3):
        if k==(0,0,0):
            continue
        r2=sum(x*x for x in k)
        w=weight(k)
        assert w*w <= 4*r2
        assert 3*w*w >= r2


def test_multimode_critical_weighted_energy_squared_bound():
    # Finite Fourier amplitude squares, with rational exact arithmetic.
    modes=[(1,0,0),(3,0,0),(1,1,1),(5,3,1),(9,2,0)]
    mass=[F(1,3),F(11,13),F(5,7),F(17,19),F(2,5)]
    E=sum(mass)
    H1=sum(sum(x*x for x in k)*e for k,e in zip(modes,mass))
    X=sum(weight(k)*e for k,e in zip(modes,mass))
    assert X*X < 4*E*H1


def test_global_residence_bound_by_exact_energy_dissipation_identity():
    # E'=-2nu H1, X²<=4 E H1 implies the interval square-energy bound.
    t0,T,nu,E0=S.symbols('t0 T nu E0', positive=True)
    t=S.symbols('t', real=True)
    E=E0*S.exp(-2*nu*t)
    H1=-S.diff(E,t)/(2*nu)
    majorant=4*E*H1
    antiderivative=S.integrate(majorant,t)
    assert S.simplify(antiderivative+E**2/nu)==0
    assert S.simplify(
        antiderivative.subs(t,T)-antiderivative.subs(t,t0)
        - (E.subs(t,t0)**2-E.subs(t,T)**2)/nu
    )==0


def test_real_divergence_free_heat_shear_global_ratio():
    # Real +/-(n,0,0) mode pair, transverse (0,a,0), no nonlinearity.
    n,nu,a,t=S.symbols('n nu a t', positive=True)
    w=S.symbols('w',positive=True)
    E=2*a*a*S.exp(-2*nu*n*n*t)
    X=2*w*a*a*S.exp(-2*nu*n*n*t)
    D1=2*n*n*a*a*S.exp(-2*nu*n*n*t)
    assert S.simplify(S.diff(E,t)+2*nu*D1)==0
    integral=S.integrate(X**2,(t,0,S.oo))
    assert S.simplify(integral / ((2*a*a)**2/nu)-w*w/(4*n*n))==0


def test_literal_cube_dyadic_constant_one_is_sharp():
    # For n=2^(j-1)+1, w=2^j, squared ratio tends exactly to 1.
    x=S.symbols('x',positive=True)
    ratio=(x/(x+1))**2
    assert S.limit(ratio,x,S.oo)==1
    previous=F(0)
    for index in range(2,15):
        n=2**(index-1)+1
        w=weight((n,0,0))
        assert w==2**index
        r=F(w*w,4*n*n)
        assert previous<r<1
        previous=r
    assert 1-previous<F(1,1000)


def test_supercritical_residence_measure_chebyshev():
    # If B=nu²/C², measure{t: X(t)>B} <= E0²/(nu B²).
    nu=F(7,5)
    E0=F(13,3)
    B=F(2,3)
    budget=E0**2/nu
    max_bad_length=budget/B**2
    assert max_bad_length==E0**2/(nu*B**2)
    assert max_bad_length>0
    # This does not say the bad set is contiguous.


def test_improved_l2_averaging_threshold_exact():
    # Average of X² over L=z/nu <= E(t0)²/z, so some time has
    # X<=E(t0)/sqrt(z), improving the old sqrt(2) coefficient.
    nu,C,E0,z=S.symbols('nu C E0 z', positive=True)
    B=nu**2/C**2
    A=C**2*E0/nu**2
    t0=S.log(A/S.sqrt(z))/(2*nu)
    assert S.simplify((E0*S.exp(-2*nu*t0))**2/z-B**2)==0


def test_optimised_recovery_is_monotone_in_scaled_initial_energy():
    A=S.symbols('A',positive=True)
    f_small=A**2
    f_large=S.Rational(1,4)+S.log(2*A)/2
    assert S.simplify(f_small.subs(A,S.Rational(1,2))-f_large.subs(A,S.Rational(1,2)))==0
    assert S.diff(f_small,A)==2*A
    assert S.diff(f_large,A)==1/(2*A)
    for aa in [S.Rational(1,16),S.Rational(1,3),S.Rational(1,2),1,10]:
        val=lambda x: x*x if x<=S.Rational(1,2) else S.Rational(1,4)+S.log(2*x)/2
        assert S.N(val(aa)) <= S.N(val(S.sqrt(2)*aa))


def test_critical_small_data_logistic_pointwise_envelope():
    # On X<=nu²/C², D>=X and X'<=-(2nu-C sqrt(X))X.
    # With y=sqrt(X), y'<=-nu*y+(C/2)*y².
    t,nu,C=S.symbols('t nu C',positive=True)
    y=2*nu/(C*(1+S.exp(nu*t)))
    assert S.simplify(S.diff(y,t)+nu*y-C*y*y/2)==0
    assert S.simplify(y.subs(t,0)-nu/C)==0
    assert S.limit(y,t,S.oo)==0
    X=S.simplify(y*y)
    assert S.simplify(X/(nu**2/C**2)-4/(1+S.exp(nu*t))**2)==0
    assert S.limit(X*S.exp(2*nu*t),t,S.oo)==4*nu**2/C**2


def test_residence_alone_cannot_bound_pointwise_critical_peak():
    # Synthetic nonnegative spikes illustrate the missing pointwise gate.
    # These are NOT physical PDE solution trajectories.
    height=S.symbols('height',positive=True)
    budget=S.symbols('budget',positive=True)
    assert S.simplify(height**2*(budget/height**2)-budget)==0
    assert S.limit(height,height,S.oo)==S.oo
