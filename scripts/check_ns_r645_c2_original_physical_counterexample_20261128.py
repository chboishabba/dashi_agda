#!/usr/bin/env python3
"""Exact physical-real strict counterexample to UNRESTRICTED R645 C2 at C=1.

This is NOT a Navier--Stokes blowup or nonexistence proof. On a genuine
smooth local periodic finite Galerkin trajectory with the user-selected
nonzero cutoff cube C=1, the literal dyadic max-norm critical weight is
w(k)=2^ceil(log2 ||k||_inf)=1 for every nonzero retained mode. Therefore
the physical unforced energy cancellation makes critical production zero.

R645 demands, for any terminal and some retained δ>0:
  int P'_C <= (2ν-δ) int D'_C + int R406_C .
We give a real/divergence-free/mean-zero/conjugate Fourier state at ν=1,
scale its velocity by 2, and show already at time zero
  P'_1(0) - 2ν D'_1(0) - R406_1(0) > 0.
Since the finite Galerkin RHS and R406 are continuous, this inequality
persists for a small positive time; integrating refutes the universal
R645 analytic premise on the original intended physical-real carrier.
The literal Agda rational field has not yet been extended to the required
sqrt(2)/sqrt(3) helical values, so this is NOT an Agda kernel inhabitant
or a formal theorem about a rational-only artificial helical surrogate.

Reuse existing exact script and R225/R388/R406/R652/R687 original source;
do not build another Fourier evaluator.
"""
# Fail closed: Python -O strips all assert statements used by this exact
# finite physical source checker. Never print PASS in optimized mode.
if not __debug__:
    raise RuntimeError("NS exact physical regression requires asserts: refuse python -O")

from collections import defaultdict
from sympy import I, S, Matrix, simplify
from check_ns_r726_signed_defect_physical_source_exact_20261128 import (
    POSITIVE, ZERO, add, neg, ksq, dot, pair, transverse, physical_certificate
)

def physical_critical_initial(values):
    u={k:Matrix(v) for k,v in values.items()}
    for k,v in list(u.items()):
        assert dot(k,v)==0
        assert neg(k) not in u
        u[neg(k)] = v.conjugate()
    nonlinear=defaultdict(lambda: ZERO.copy())
    for p in u:
        for q in u:
            k=add(p,q)
            if k != (0,0,0) and max(map(abs,k))<=1:
                nonlinear[k] += dot(u[p],Matrix(q))*u[q]
    forcing={k:-I*transverse(k,v) for k,v in nonlinear.items()}
    # All C=1 nonzero modes have max-norm 1 and exact dyadic weight 1.
    production=simplify(2*sum(
        (pair(u[k],forcing.get(k,ZERO)) for k in u),S.Zero))
    dissipation=simplify(sum(
        (ksq(k)*pair(v,v) for k,v in u.items()),S.Zero))
    assert all(max(map(abs,k)) == 1 for k in u)
    assert production==0
    assert dissipation.is_positive is True
    return production,dissipation

def main():
    origin,entries=physical_certificate(POSITIVE,viscosity=S.One)
    P,D=physical_critical_initial(POSITIVE)
    assert entries==316 and P==0 and D==108
    r=origin['r406']
    expected=(
      -S(1216)/9-S(317)/9*S(3)**S.Half
      -S(77)/4*S(6)**S.Half+S(815)/12*S(2)**S.Half
    )
    assert simplify(r-expected)==0
    assert (r+S(69)/2).is_negative is True  # exact radical comparison

    # Original 369 sign grade: global velocity inversion preserves D
    # and every even quadratic observer but reverses genuine R406 quintic.
    inverted={k:tuple(-x for x in v) for k,v in POSITIVE.items()}
    reflected,nref=physical_certificate(inverted,viscosity=S.One)
    Pref,Dref=physical_critical_initial(inverted)
    assert nref==316 and Pref==0 and Dref==D
    assert simplify(reflected['r406']+r)==0
    assert simplify(reflected['combined']+origin['combined'])==0

    amplified={k:tuple(2*x for x in v) for k,v in POSITIVE.items()}
    big,entries2=physical_certificate(amplified,viscosity=S.One)
    P2,D2=physical_critical_initial(amplified)
    assert entries2==316 and P2==0 and D2==432
    assert simplify(big['r406']-32*r)==0
    assert simplify(big['combined']-32*origin['combined'])==0
    assert simplify(big['forcing_full']-32*origin['forcing_full'])==0
    assert (big['r406']+1104).is_negative is True
    # For ANY δ>=0: (2-δ)*432+R406 <= 864+R406 < -240.
    uncompensated = simplify(P2-2*D2-big['r406'])
    assert (uncompensated-240).is_positive is True
    for delta in (S.Zero,S(1)/100,S.One,S(10)):
        gap=simplify(P2-(2-delta)*D2-big['r406'])
        assert gap.is_positive is True

    print('PASS exact original C=1 physical-real C2 obstruction')
    print('all 316 ordered incidences retained per original state')
    print('unscaled production,dissipation,R406:',P,D,r)
    print('scaled production,dissipation,R406:',P2,D2,big['r406'])
    print('same energy/dissipation inverted velocity R406:',reflected['r406'])
    print('minimum violation margin (δ=0):',uncompensated)
    print('source conditional R645 fails on a sufficiently short real Galerkin interval')
    print('no unrestricted NS regularity or kernel claim')
if __name__=='__main__':main()
