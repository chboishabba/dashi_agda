#!/usr/bin/env python3
"""Exact SymPy/Fraction crosscut; NOT a Clay or Agda/Lean kernel receipt.

Sources: original DASHI R829/R854/R855; PR #1271 R734 physical W2 NO-GO;
PR #1503 R445 sharp likelihood ratio and weighted exterior influence.
The toy plaquette hypergraph checks finite Gibbs locality, NOT the
actual 1024-link SU(N) blocked effective vs bare target measure.
"""
from fractions import Fraction
from itertools import product
from math import prod
import json
import sympy as S

r0 = -S.Rational(28273644, 125)
L = S.Integer(391309593930357307785216)
T = S.Rational(226189, 3938540454339300631433585885184)

def r855():
    point = S.factor(-r0/(L*T))
    integ = 2*point
    assert point == S.Rational(284574905427456, 28273625)
    assert (S.floor(point), S.ceiling(point), S.floor(integ), S.ceiling(integ)) == (
        10065030, 10065031, 20130061, 20130062)
    p0=S.factor(r0 + 10065030*L*T)
    p1=S.factor(r0 + 10065031*L*T)
    i0=S.factor(r0*T + 20130061*L*T*T/2)
    i1=S.factor(r0*T + 20130062*L*T*T/2)
    assert p0<0 and p1>0 and i0<0 and i1>0
    assert p0 == -S.Rational(3598951,209688000)
    assert p1 == S.Rational(6679919,1258128000)
    return dict(pointwise_max=str(point),integral_max=str(integ),
      safe_pointwise_integer=10065030,first_unsafe_pointwise_integer=10065031,
      safe_integral_integer=20130061,first_unsafe_integral_integer=20130062,
      pointwise_safe=str(p0),pointwise_next=str(p1),
      integrated_safe=str(i0),integrated_next=str(i1))

def total_variation(a,b):
    return sum((abs(x-y) for x,y in zip(a,b)),Fraction(0))/2

def gibbs_conditional(xs,y,plaquettes):
    def weight(x):
        z=x+y
        exponent=sum(coef*prod((1 if z[j] else -1 for j in ids))
                     for ids,coef in plaquettes)
        return Fraction(2)**exponent
    weights=[weight(x) for x in xs]
    return [v/sum(weights) for v in weights]

def finite_gibbs():
    # Two interior bits; four exterior bits. Mixed plaquettes meet sites 2,3.
    # Exterior-only plaquettes can change the partition weight but cancel
    # from the normalized conditional interior distribution.
    xs=list(product((0,1),repeat=2))
    ys=list(product((0,1),repeat=4))
    plaquettes=[((0,2),1),((1,3),2),((0,1,3),1),
                ((3,4),1),((4,5),-1)]
    near=[];far=[]
    for j in range(4):
        changes=[]
        for y in ys:
            y2=y[:j]+(1-y[j],)+y[j+1:]
            changes.append(total_variation(gibbs_conditional(xs,y,plaquettes),
                                           gibbs_conditional(xs,y2,plaquettes)))
        (near if j<2 else far).append(max(changes))
    assert near==[Fraction(195,406),Fraction(33,35)]
    assert far==[0,0]
    cases=0
    # Exact finite general reweighting: TV <= chord bound <= sharp envelope.
    for raw in product((1,2,3),repeat=3):
        q=[Fraction(v,sum(raw)) for v in raw]
        for ws in product((1,2,4),repeat=3):
            z=sum((qv*w for qv,w in zip(q,ws)),Fraction(0))
            p=[qv*w/z for qv,w in zip(q,ws)]
            tv=total_variation(q,p);lo,hi=min(ws),max(ws)
            if lo==hi: assert tv==0
            else:
                chord=(z-lo)*(hi-z)/(z*(hi-lo))
                assert tv<=chord
                sharp=(S.sqrt(hi)-S.sqrt(lo))/(S.sqrt(hi)+S.sqrt(lo))
                assert S.simplify(S.Rational(tv.numerator,tv.denominator)-sharp)<=0
            cases+=1
    assert cases==729
    assert total_variation([Fraction(4,5),Fraction(1,5)],
                           [Fraction(1,5),Fraction(4,5)])==Fraction(3,5)
    return dict(near=list(map(str,near)),far=list(map(str,far)),
                exact_weight_cases=cases,far_conditional_tests=32)

def q_slot_countermodel():
    output=S.Matrix([1,0,0]);derivative=S.Matrix([0,1,0])
    directional=(output.dot(derivative))**2
    assert directional==0
    # An arbitrary selected signed scalar of 1 is not this square.
    # The physical identification hypothesis is substantive.
    selected_scalar=S.Integer(1)
    assert selected_scalar>directional
    return dict(directional='0',arbitrary_selected_scalar='1',
      physical_slot_identity_not_automatic=True)

if __name__=='__main__':
    print(json.dumps(dict(result="PASS",sympy=S.__version__,
      r855=r855(),finite_gibbs=finite_gibbs(),q_slot=q_slot_countermodel(),
      actual_Wilson_blocked_measure_bound=False,
      actual_NS_Galerkin_rate_bound=False,
      universal_Clay_proof=False,agda_kernel=False,lean_kernel=False),
      sort_keys=True,indent=2))
