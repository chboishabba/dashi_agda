"""Exact arithmetic acceptance for the periodic R734 dyadic critical estimate.

Scientific attribution: Fujita--Kato classical small H^{1/2} global result;
new work: R734's original sharp-cube dyadic weight and its constants.
The PDE Sobolev embeddings are explicit mathematical inputs, not certified
by these finite scalar tests or any Agda kernel.
"""
from fractions import Fraction as F
from itertools import combinations


def dyadic_weight(k):
    m = max(map(abs, k))
    assert m >= 1
    return 1 << (m - 1).bit_length()


def test_cube_dyadic_weight_radius_comparison_exact_squared():
    # r/sqrt(3) <= w < 2r, valid for all nonzero integer modes.
    for x in range(-9, 10):
        for y in range(-9, 10):
            for z in range(-9, 10):
                if (x,y,z)==(0,0,0):
                    continue
                w=dyadic_weight((x,y,z));r2=x*x+y*y+z*z
                assert w*w*3 >= r2
                assert w*w < 4*r2


def test_cauchy_interpolation_difference_of_squares():
    # We choose integer radii (axis modes) so the Sobolev interpolation
    # determinant can be checked exactly, without an approximate sqrt.
    radii=[1,2,4,8,16]
    energies=[F(4,9),F(5,7),F(1,11),F(13,5),F(7,3)]
    hhalf=sum((r*e for r,e in zip(radii,energies)),F(0))
    hone=sum((r*r*e for r,e in zip(radii,energies)),F(0))
    hthree=sum((r*r*r*e for r,e in zip(radii,energies)),F(0))
    sumsq=sum((radii[i]*radii[j]*(radii[i]-radii[j])**2 * energies[i]*energies[j]
               for i,j in combinations(range(len(radii)),2)),F(0))
    assert hhalf*hthree-hone**2 == sumsq
    assert sumsq>0


def test_critical_absorption_bootstrap_scalars():
    # C=4*3^(3/4)*C6*C3 is a finite dimensionless embedding constant.
    # delta=2*nu-C sqrt(X0)>0 implies X(t)+delta*int(D) <= X0.
    # Ratios y=C sqrt(X0)/nu tested exactly.
    nu=F(3,4)
    for ratio in [F(1,4),F(1,1),F(7,4),F(199,100)]:
        coefficient=nu*ratio
        delta=2*nu-coefficient
        assert delta>0
        assert delta<=2*nu
        for D in [F(0),F(1,10),F(12,5)]:
            P_upper=coefficient*D
            assert P_upper-2*nu*D <= -delta*D


def test_small_critical_data_allows_large_enstrophy():
    # Real, transverse shear modes +/- (n,0,0), each Fourier coefficient
    # having norm n^(-3/4): with n=2^j, dyadic w=n.
    # X=2*n^(-1/2) tends to 0 while H1^2=2*n^(1/2) diverges.
    for j in (2,4,8,12):
        n=2**j
        # Square inequalities avoid approximate n^(1/2)
        x2=F(4,n)
        enstrophy2=F(4*n)
        assert x2*enstrophy2==16
    assert F(4,2**12)<F(4,2**2)
    assert F(4*2**12)>F(4*2**2)


def test_high_amplitude_example_does_not_enter_small_data_lane():
    # The known signed R734 obstruction is not erased: the replacement
    # estimate only supplies a positive damping coefficient if smallness
    # is independently established, NOT for all large initial data.
    nu=F(1)
    effective_nonlin_over_dissipation=F(5,2)*nu
    assert 2*nu-effective_nonlin_over_dissipation<0



def test_eventual_critical_entry_from_energy_average_exact():
    # Energy inequality E'+2nu H1^2=0, so on an interval of length 1/nu
    # there exists s with H1^2(s)<=E(t0)/2. For that s:
    # X(s) <= 2 H1/2^2 <= 2 sqrt(E(s)*H1^2(s))
    #      <= sqrt(2)*E(t0).
    # Fix E(t0)<=nu^2/(sqrt(2)*Ccrit^2); then X(s)<=nu^2/Ccrit^2.
    # This test uses the exactly squared inequalities and Ccrit=1 fixture.
    nu=F(3,2); Ccrit=F(1)
    e0_squared_bound=nu**4/(2*Ccrit**4)
    # E0 <= nu^2/(sqrt(2)*C^2) iff E0^2 <= nu^4/(2*C^4).
    for e0 in [F(1,2),F(3,2)]:
        assert e0*e0 <= e0_squared_bound
        # (sqrt(2)*E0)^2 <= (nu^2/C^2)^2
        assert 2*e0*e0 <= nu**4/Ccrit**4


def test_eventual_critical_dissipation_margin_exact():
    # Once X<=nu^2/Ccrit^2 at s, Ccrit sqrt(X)<=nu and
    # X'+nu D<=0 subsequently. The small class is invariant.
    nu=F(2,1)
    Ccrit=F(5,4)
    xthreshold=nu**2/Ccrit**2
    assert Ccrit**2*xthreshold==nu**2
    assert 2*nu-nu==nu
    # With X(t_enter)<=xthreshold, the right-hand post-entry budget
    # is independent of the initial kinetic energy E0 and cutoff N.



def test_optimal_averaging_interval_calculus_exact():
    # Set z=nu*L, A=sqrt(2)*Ccrit^2*E0/nu^2.
    # When 0<z<A^2, t_enter*nu=z+0.5*log(A/sqrt(z)).
    # The derivative is 1-1/(4z), minimized at z=1/4.
    import sympy as S
    z,A=S.symbols('z A', positive=True)
    f=z+S.Rational(1,2)*S.log(A/S.sqrt(z))
    assert S.simplify(S.diff(f,z)-(1-1/(4*z)))==0
    assert S.simplify(S.diff(f,z,2)-1/(4*z*z))==0
    assert S.simplify(S.diff(f,z).subs(z,S.Rational(1,4)))==0


def test_optimal_averaging_interval_piecewise_and_continuous():
    import sympy as S
    A=S.symbols('A', positive=True)
    small=A*A
    large=S.Rational(1,4)+S.log(2*A)/2
    assert S.simplify((small-large).subs(A,S.Rational(1,2)))==0
    # At A<1/2, choosing z=A^2 removes the waiting-for-decay term.
    assert S.simplify(S.log(A/S.sqrt(A*A)))==0
    for a in [S.Rational(1,10), S.Rational(1,3)]:
        assert 0<a<S.Rational(1,2)
        assert 0<small.subs(A,a)<S.Rational(1,4)
    # At A>1/2, choosing z=1/4 yields t0=log(2A)/(2nu).
    assert S.simplify(S.log(A/S.sqrt(S.Rational(1,4)))-S.log(2*A))==0
