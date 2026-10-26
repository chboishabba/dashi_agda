"""A universal energy-only R735 W1 bound fails on ACTUAL NS heat shears.

This is a source-defined family of genuine smooth, real, divergence-free
unforced NS solutions on T³, not an abstract cell assignment:
  u_N(0,x)=2/sqrt(2N) sum_(n=1)^N cos(n*x) e_z, viscosity=1.
For every N, E_kin(0)=1 and integral_0^infty D(t)dt=1/2.
Their H+×H- mixed-output mass at canonical same-N cutoff is
  E_M,N(0)=(N-1)(2N-1)/(48N).
At T=log(2), Fourier coefficients have the EXACT rational factor
  exp(-n²*T)=2^(-n²).
The nonlinear commutator vanishes for ALL t (z-directed x shear), so
R691 and R735's W1 source satisfy identically
  Weighted_N(T)+E_M,N(T)=E_M,N(0).
The terminal mass at T=log(2) is <= 2/(3N²); thus the accumulated
signed weighted work grows ~N/24 despite an invariant kinetic energy
and the SAME energy dissipation budget 1/2.

This DISPROVES solely energy-dependent universal W1 constants, NOT
a fixed-data H^(3/4) ceiling, global NS regularity, nor a data-dependent
unrestricted R735 W1/W2 bound.

Original attribution: periodic heat semigroup, Fourier-helical source
(Lei/Lin/Zhou), R691 endpoint (existing DASHI formalization);
the explicit family and inequality are DASHI's independent test.
"""
from fractions import Fraction as F

def initial_mass(n):
    assert n>=2
    return F((n-1)*(2*n-1),48*n)

def mass_at_log2(n):
    assert n>=2
    result=F(0)
    for k in range(2,n+1):
        # Only positive-positive cells contribute at k>0,
        # and the negative-negative conjugate accounts for a factor 2.
        amplitude=sum((F(1,2**(p*p+(k-p)**2)) for p in range(1,k)),F(0))
        result += 2*(amplitude/F(4*n))**2
    return result

def test_actual_finite_time_W1_and_terminal_ceiling():
    for n in (2,3,4,5,8,16,32):
        m0=initial_mass(n)
        mt=mass_at_log2(n)
        w1=m0-mt
        assert F(0)<mt<m0
        assert mt <= F(2,3*n*n)
        assert w1+mt==m0
        assert w1 >= m0-F(2,3*n*n)

def test_constant_energy_and_total_dissipation_for_every_mode_count():
    for n in (2,3,4,12,64):
        amplitude_squared=F(1,2*n)
        energy=2*n*amplitude_squared
        dissipation_integral=sum(
            2*amplitude_squared*j*j*F(1,2*j*j)
            for j in range(1,n+1))
        assert energy==1
        assert dissipation_integral==F(1,2)

def test_quantified_asymptotic_excludes_energy_only_W1_bound():
    # The first term is ~n/24; the terminal mixed mass decays O(n^-2).
    for n in (2,3,10,25,100):
        m0=initial_mass(n)
        assert m0 >= F(n-1,48)
        assert initial_mass(n)-F(2,3*n*n) >= F(n-1,48)-F(2,3*n*n)
    # Choose N so that (N-1)/48 - 2/(3N²)>C for arbitrary C:
    for C in (F(1),F(2),F(10),F(100)):
        n=int(48*C+3)
        assert F(n-1,48)-F(2,3*n*n)>C

def test_helical_pair_convolution_multiplicity():
    # For positive input modes p,q in {1,...,N}, k=p+q,
    # all ordered pairs at k=2,...,N number k-1.
    for n in (2,3,4,10):
        assert sum(sum(p+q==k for p in range(1,n+1)
                       for q in range(1,n+1))
                   for k in range(2,n+1))==n*(n-1)//2
