#!/usr/bin/env python3
"""RH/GRH P0: source-original fourth-primitive, actual zeta counting, RvM no-go.

References:
 - dashi_lean4 Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean
   OuterFourthPrimitiveUniformBound, outerSymmetricDiscrepancyFourthPrimitive_eq_physical
 - dashi_lean4 Synthesis/RiemannZetaMuZeroCountOneSided.lean
   exists_zetaCount_*_muIntegral_*_logError
 - Zeta23/GammaFacts/Mu.lean (mu = (Re digamma(1/4+ix/2)-log(pi))/(2pi)).

Does not construct the existential original selected quartic W(t). Numerical zero
checks do NOT prove analytic continuation, RH/GRH or a global strict signed bound.
"""
import bisect
import math
import numpy as np
import sympy as sp
import mpmath as mp
from scipy.integrate import quad
from scipy.special import loggamma, digamma

s,S,b,s0,r,Q,eta,C,L=sp.symbols('s S b s0 r Q eta C L',positive=True)
# Same original 4th Cesaro primitive: one unit zero-count atom outside s0.
assert sp.simplify(sp.integrate((S-s)**3/6,(s,b,S))-(S-b)**4/24)==0
assert sp.simplify(((r*Q-r*b)**4/24)/r**4-(Q-b)**4/24)==0
assert sp.simplify(sp.integrate((S-s)**3/6,(s,s0,S))-(S-s0)**4/24)==0
# RvM |D(s)| <= 2 C log(t+rQ+4) => ONLY the O(r^4 log t) envelope:
assert sp.simplify(2*C*L*sp.integrate((S-s)**3/6,(s,s0,S))-
                   C*L*(S-s0)**4/12)==0
# For any fixed b between eta and Q: one atom perturbs D by at most 1, but
# the fourth primitive changes by r^4*(Q-b)^4/24; unbounded as t grows.
assert sp.simplify(sp.diff((r*(Q-b))**4/24,r)-r**3*(Q-b)**4/6)==0
print('PASS exact fourth primitive/Fubini and O(r^4 log t) RvM-only envelope')

T=200.0
r0=T/16.0
eta0=1.0/(math.pi+1.0)
s00=r0*eta0

# Precision independent actual-N reference: scipy gamma-density vs mpmath.
def mu(x):
    return (float(np.real(digamma(.25+.5j*x)))-math.log(math.pi))/(2*math.pi)
def M(A,B):
    # Exact antiderivative of the ORIGINAL gamma/digamma mu; no Stirling recut.
    return (float(np.imag(loggamma(.25+.5j*B)-loggamma(.25+.5j*A)))
            -(B-A)*math.log(math.pi)/2)/math.pi
for A,B in ((100,150),(187.5,212.5),(100,300)):
    integral=quad(mu,A,B,epsabs=2e-9)[0]
    assert abs(M(A,B)-integral)<3e-11, (A,B,M(A,B),integral)
print('PASS original mu exact Gamma antiderivative against digamma quadrature')

mp.mp.dps=35
out=[]
for Q0 in (4.,8.):
    outer=r0*Q0
    A,B=T-outer,T+outer
    # At B=300, mp.nzeros(300)=138. All numerical zeros within [A,B].
    nmax=int(mp.nzeros(B))
    zs=[float(mp.im(mp.zetazero(n))) for n in range(1,nmax+1)]
    valid=[z for z in zs if A<z<=B]
    abs_offsets=sorted(abs(z-T) for z in valid)
    def N(sv):
        return bisect.bisect_right(abs_offsets,sv)
    def D(sv):
        return N(sv)-M(T-sv,T+sv)
    # Fourth primitive as its direct weighted RvM-discrepancy integral.
    knots=[s00]+[v for v in abs_offsets if s00<v<outer]+[outer]
    from_direct=sum(quad(lambda x:(outer-x)**3*D(x)/6,u,v,epsabs=1e-5)[0]
                    for u,v in zip(knots[:-1],knots[1:]))
    # Equivalent source original quartic cap via Fubini/staircase atom sum.
    zero_cap=sum(max(0.,outer-max(s00,abs(z-T)))**4/24 for z in valid)
    def cap_y(y):
        return max(0.,outer-max(s00,abs(y-T)))**4/24
    mu_cap=sum(quad(lambda y:cap_y(y)*mu(y),a,b,epsabs=2e-5)[0]
               for a,b in zip((A,T-s00,T+s00),(T-s00,T+s00,B)))
    from_cap=zero_cap-mu_cap
    assert abs(from_cap-from_direct)<3e-3, (Q0,from_cap,from_direct)
    # Exact single-atom P4 increment at beta? independent of horizontal.
    b0=(eta0+Q0)/2
    extra=(r0*(Q0-b0))**4/24
    assert abs(extra/r0**4-(Q0-b0)**4/24)<1e-12
    # Sample of real N-mu; positive and negative outcomes tested separately.
    ds=[(round(v,4),round(D(r0*v),6)) for v in [eta0,1.0,2.,Q0]]
    out.append((Q0,len(valid),from_direct,from_cap,extra,ds))
    print(f'ACTUAL ζ t=200 Q={Q0:g} N={len(valid)} P4={from_direct:.8f} '
          f'cap={from_cap:.8f} P4/r^4={from_direct/r0**4:.8f} atom_increment/r^4={extra/r0**4:.8f}')
    print('  D(RvM) samples:',ds)


# SINGLE global symmetry-compatible synthetic positive-ordinate perturbation:
# append ordinates gamma_n=(17/16)*4^n, n>=4, with their negative conjugates.
# This changes any positive interval count by <= 1+log_4(max(B,1)); it thus
# retains an O(log B) arbitrary-endpoint RvM discrepancy, with enlarged C.
# At t_n=4^n, Q=4, only gamma_n is inside [3t_n/4,5t_n/4].
# The fourth cap is exactly (27/8)*(t_n/16)^4 and UNBOUNDED in n.
from fractions import Fraction as F
for n in range(4,10):
    tn=4**n
    rn=F(tn,16)
    candidate=[F(17,16)*4**m for m in range(4,12)]
    inside=[x for x in candidate if F(3,4)*tn < x <= F(5,4)*tn]
    assert inside == [F(17,16)*tn]
    cap= (rn*4 - (inside[0]-tn))**4 / 24
    assert cap == F(27,8)*rn**4
    assert cap/rn**4==F(27,8)
    print(f'SYNTHETIC lacunary n={n}: r^4 witness cap={cap}, ratio=27/8')
print('PASS single global lacunary count perturbation retains logarithmic RvM scale but has unbounded quartic primitive')

# Under a perturbed counting measure with one atom at t+r*b, every interval
# count differs by at most one. Original RvM hypotheses cannot bound P4 by
# an absolute constant from its discrepancy assumption alone.
assert all(math.isfinite(float(x[2])) for x in out)
print('PASS actual numerical zeta count vs exact mu, original symmetric P4 via two independent expressions')
print('OPEN original full signed H+S<4d+I and selected W, horizontal zero locations, uniform-in-t fourth primitive')
