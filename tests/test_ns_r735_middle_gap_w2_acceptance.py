"""Exact R735 temporal and critical-weight acceptance tests.

Classical unforced Navier-Stokes Galerkin energy/H1 comparison is credited
to Leray and standard strong-solution theory. R691/R734/R735 and the
literal dyadic critical carrier belong to their existing DASHI owners.
These are exact *scalar* structural checks, not physical continuum
global regularity, nor Agda/Lean kernel-verified theorems.
"""
from fractions import Fraction as F
import sympy as s


def test_large_h1_gap_invariant_normal_form():
    nu,K,r=s.symbols('nu K r',positive=True)
    dstar=nu**2/s.sqrt(2*K)
    D0=r*dstar
    tlocal=nu**3/(4*K*D0**2)
    assert s.simplify(tlocal-1/(2*nu*r*r))==0
    # For all r>1, early bound ends before 1/(2nu), whereas the
    # common eventual entry starts no earlier than 1/nu.
    for val in [s.Rational(11,10),2,10,100]:
        t=s.simplify(tlocal.subs({nu:2,K:3,r:val}))
        assert t < s.Rational(1,4)
        assert s.Rational(1,2)-t > s.Rational(1,4)


def test_fixed_energy_real_heat_shear_w1_divergence_is_within_gap():
    # REAL unforced shear 2/sqrt(2N)*sum_(n=1)^N cos(nx)*e_z.
    # Normalized Fourier E0=1, D0=(N+1)(2N+1)/6.
    # At K=nu=1, entry=1; local end<log(2)<1.
    for N in (4,5,10,30,100):
        E0=s.Integer(1)
        D0=s.Rational((N+1)*(2*N+1),6)
        dstar=1/s.sqrt(2)
        tlocal=1/(4*D0**2)
        assert E0 < 2*dstar
        assert s.N(tlocal) < s.N(s.log(2)) < 1
        initial=F((N-1)*(2*N-1),48*N)
        terminal_upper=F(2,3*N*N)
        middle_lower=initial-terminal_upper
        assert middle_lower>F(0)
        assert middle_lower>=F(N-1,48)-terminal_upper
    # Do not claim positivity from the loose terminal estimate at N=2/3:
    # it becomes useful at N>=4; the full PDE example exists for all N.


def test_fixed_initial_energy_middle_w1_has_no_universal_bound():
    # No bound dependent only on E0=1 and nu=1 is possible for
    # W_N(log2) across these different smooth data and cutoffs.
    for C in (F(1),F(3),F(100),F(1000)):
        N=48*int(C)+100
        initial=F((N-1)*(2*N-1),48*N)
        terminal_upper=F(2,3*N*N)
        assert initial-terminal_upper>C


def test_r734_w2_is_equivalent_to_signed_r691_commutator_payment():
    xT,x0,eT,e0,w,cint,margin,d=s.symbols(
        'xT x0 eT e0 w cint margin d')
    # R734 W2: [X_T-12E_T]-[X_0-12E_0]+margin*D<=12W.
    lhs=(xT-12*eT)-(x0-12*e0)+margin*d-12*w
    # R691: W=Cint-(E_T-E_0), same cutoff and trajectory.
    rhs=s.expand(lhs.subs(w,cint-eT+e0))
    assert s.expand(rhs-(xT-x0+margin*d-12*cint))==0
    assert s.expand(
        lhs.subs(cint,w+eT-e0)-rhs.subs(cint,w+eT-e0))==0


def test_w1_bound_alone_cannot_promise_r734_w2():
    # ABSTRACT scalar consumer countermodel only, NOT a physical NS state.
    eT=s.Integer(1);e0=s.Integer(1);w=s.Integer(0);B=s.Integer(2)
    assert w+eT<=B
    x0=s.Integer(1);d=s.Integer(2);margin=s.Integer(1)
    for xT in (5,50,500):
        augmented=(xT-12*eT)-(x0-12*e0)+margin*d
        assert augmented>12*w


def test_original_r735_critical_weight_is_dyadic_Hhalf_not_H1():
    # Actual LiteralFiniteCriticalObservableFold:
    # w(k)=2^ceil(log2(||k||_infty)), not ||k||².
    # For a single real transverse pair ±(n,0,0) with Fourier E=1.
    def dyadic(k):
        return 1 << (k-1).bit_length()
    for j in range(1,11):
        n=2**j
        critical_mass=dyadic(n)
        enstrophy_mass=n*n
        assert critical_mass==n
        assert F(enstrophy_mass,critical_mass)==n
        assert critical_mass**2==enstrophy_mass
    for n in [3,5,9,17,37]:
        assert n<=dyadic(n)<2*n
