"""Exact smooth physical shear family: no E-only R699 initial mass bound.

For N>=2, u_N(x)=2/sqrt(2N)*sum_{n=1}^N cos(nx) e_z.
Every field is real, divergence free and unforced NS heat-evolving,
and sum_k |uhat_k|²=1 with uhat_(±n,0,0)=1/sqrt(2N)*e_z.

For p,q>0 the true curl-spectral mixed helical product is
  H+_p u_p × H-_q u_q = -i/(4N) e_x;
opposite-sign pairs give 0; negative-negative gives the conjugate.
At output k=2,...,N there are (k-1) positive ordered pairs.
Consequently ORIGINAL same-N cutoff mixed initial mass is
  E_M,N = (N-1)(2N-1)/(48N) ~ N/24,
despite fixed Fourier kinetic energy 1 for EVERY smooth datum.
The full generated-output mixed mass is N/12+1/(24N).
Original math: classical helical decomposition and exact arithmetic;
DASHI owns this independently constructed physical counterexample.
This is not a counterexample to global NS regularity, R735 W1 with
data-dependent bound, or R699's H^s initial-data bound.
"""
import sympy as S

def project(k,sign,u):
    kv=S.Matrix((k,0,0))
    return S.simplify((u+sign*S.I*kv.cross(u)/abs(k))/2)
def norm2(u):
    return S.simplify((S.conjugate(u).T*u)[0])

def test_exact_actual_projector_and_opposite_sign_pair():
    a=S.symbols('a',positive=True)
    z=a*S.Matrix((0,0,1))
    assert S.simplify(project(3,1,z).cross(project(4,-1,z))
                      + S.I*a*a*S.Matrix((1,0,0))/2)==S.zeros(3,1)
    assert project(3,1,z).cross(project(-4,-1,z))==S.zeros(3,1)
    assert S.simplify(project(-3,1,z).cross(project(-4,-1,z))
                      - S.I*a*a*S.Matrix((1,0,0))/2)==S.zeros(3,1)

def test_unforced_shear_exact_cutoff_mixed_mass_grows_at_fixed_energy():
    for N in (2,3,4,5,10,32,100,1000):
        a2=S.Rational(1,2*N)
        assert 2*N*a2==1
        # Inside the ORIGINAL same-N nonzero output cutoff: k=2,..,N.
        mass=2*sum((S.Rational(1,4)*a2*a2*(k-1)**2 for k in range(2,N+1)))
        exact=S.Rational((N-1)*(2*N-1),48*N)
        assert mass==exact
    n=S.symbols('n',integer=True,positive=True)
    assert S.limit(((n-1)*(2*n-1)/(48*n))/n,n,S.oo)==S.Rational(1,24)

def test_full_output_mass_and_fixed_N_energy_only_no_go():
    for n in (2,3,4,5,10,30):
        a2=S.Rational(1,2*n)
        def count(k):
            return max(0,min(n,k-1)-max(1,k-n)+1)
        mass=2*sum((a2*a2*count(k)**2/S.Integer(4)
                    for k in range(2,2*n+1)))
        assert mass==S.Rational(n,12)+S.Rational(1,24*n)
    # For arbitrary fixed constant C, choose N>24*C+2;
    # E_M,N grows at least linearly, while E(u_N)=1.
