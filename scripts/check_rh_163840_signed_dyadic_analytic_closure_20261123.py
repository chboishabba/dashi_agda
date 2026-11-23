#!/usr/bin/env python3
"""RH/GRH P0: exact signed 15-bit gamma-tail action and smooth-test no-go.

The original selected quartic W is NOT constructed here. Independent local
SymPy/mpmath acceptance; not Agda/Lean kernel and not a zero-side proof.
"""
from fractions import Fraction
from itertools import product
import math
import sympy as sp
import mpmath as mp

N=1<<15
q,u=sp.symbols("q u",positive=True)
qu=8*u**(-sp.Rational(1,5))
assert N==32768 and 5*8**5==163840
assert sp.simplify(-sp.diff(qu,u)/qu**6-sp.Rational(1,163840))==0
assert sp.integrate(q**-6,(q,8,sp.oo))==sp.Rational(1,163840)
assert sp.simplify(sp.integrate(q**-6,(q,16,sp.oo))/sp.integrate(q**-6,(q,8,sp.oo))-sp.Rational(1,32))==0
assert Fraction(1024,N)==Fraction(1,32)
print("PASS exact tail Jacobian / 32768 cells / q=16 cell 1024")

# Mask bit 6 reverses the physical ordinate sign. Bits 0..5 are
# cell-permutation coordinates (NOT the native Heisenberg generators).
def act(mask,sign,k,theta):
    assert 0<=mask<128 and sign in (-1,1) and 0<=k<N and 0<theta<1
    return (-sign if mask&64 else sign,k^(mask&63),theta)

for m,n in product(range(128),repeat=2):
    for k in (0,1024,N-1):
        assert act(m,*act(n,1,k,Fraction(1,3)))==act(m^n,1,k,Fraction(1,3))
for m in range(128):
    for sign,k,theta in product((-1,1),(0,1,31,32,1023,1024,32704,32735,N-1),(Fraction(1,5),Fraction(1,2),Fraction(4,5))):
        assert act(m,*act(m,sign,k,theta))==(sign,k,theta)
for m in range(64):
    assert len({k^m for k in range(N)})==N
print("PASS 128 signed masks, 4096 mask compositions, all 64 full-cell permutations")

# Let k_j=N-2^j. At u=k_j/N the left/right transformed u limits
# are 1 and 1-2^(j+1)/N, an exact positive discontinuity.
# For an even nonnegative C-infinity compact bump P supported in |v|<1/4
# with mass away from zero, C_P'(q)=-2*int_0^(1/4) vP(v)sin(qv)dv<0
# throughout 8<=q<=8.1. Thus a transformed C_P has a jump and
# cannot be the Fourier transform of any integrable compact profile.
for j in range(6):
    bit=1<<j
    k=N-bit
    left=Fraction(((k-1)^bit)+1,N)
    right=Fraction(k^bit,N)
    assert left==1 and left-right==Fraction(2*bit,N)
    qleft=8.
    qright=8*float(right)**(-1/5)
    assert 8<qright<8.1 and qright/4<math.pi
    # Gaussian is a SEPARATE smooth numerical fixture, not original W.
    diff=math.exp(-qleft*qleft/128)-math.exp(-qright*qright/128)
    assert diff>0
    print(f"PASS bit={j} exact jump={left-right} Gaussian discrepancy={diff:.8g}")

# The genuine ordinate C2 reflection leaves an even Gamma integrand
# unchanged. The same Gamma integration is unchanged under paired
# dyadic permutations by exact reindexing; physical test is NOT fixed.
mp.mp.dps=35
T=mp.mpf(200)
def mu(x,parity):
    return (mp.re(mp.digamma(mp.mpf("0.25")+mp.mpf(parity)/2+mp.j*x/2))-mp.log(mp.pi))/(2*mp.pi)
def delta(x,parity):
    return mu(T*(1+x/16),parity)+mu(T*(1-x/16),parity)-2*mu(T,parity)
def fixture(u,parity):
    x=8*mp.power(u,-mp.mpf(1)/5)
    return mp.exp(-x*x/128)*delta(x,parity)
def cell_integral(k,fun):
    return mp.quad(lambda theta:fun((mp.mpf(k)+theta)/N),[0,1])/N
for parity in (0,1):
    for x in map(mp.mpf,(8,16,32)):
        assert abs(delta(x,parity)-delta(-x,parity))<mp.mpf("1e-31")
    for j in range(6):
        a,b=1024,1024^(1<<j)
        direct=cell_integral(a,lambda v:fixture(v,parity))+cell_integral(b,lambda v:fixture(v,parity))
        pulled=(cell_integral(a,lambda v:fixture((mp.mpf(b)+v*N-a)/N,parity))
                +cell_integral(b,lambda v:fixture((mp.mpf(a)+v*N-b)/N,parity)))
        assert abs(direct-pulled)<mp.mpf("1e-33")
print("PASS genuine Γ reflection across q=16, six dyadic pairwise reindexings, both parities")
d,e,S=sp.symbols("d e S",nonnegative=True)
assert sp.expand(2*(2*d+e)+S-4*d)==2*e+S
print("OPEN original W(t) action admission, selected-W uniform norms, strict signed zero estimate; RH/GRH OPEN")
