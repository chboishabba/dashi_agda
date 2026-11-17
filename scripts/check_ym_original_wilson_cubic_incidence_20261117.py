#!/usr/bin/env python3
"""Original six-positive-plane periodic SU2 third Wilson moment.

Independent Haar center flips annihilate products of plaquette traces
whenever an original link has odd multiplicity.  Exact F2 incidence
checks side L=2,3,4 show that no three distinct plaquettes form an
F2-cycle. Together with E[t_p]=0 and E[t_p²]=1/4, this yields
 E[(P - sum_p t_p)^3] = P³+3P²/4, P=6L^4.
The all-L>=2 geometric lemma requires a separate universal proof.
At L=1 use the genuine commutator checker, not this formula.
Attribution: Wilson/Balaban and the original DASHI periodic SU2 owners.
"""
from itertools import product,combinations
from fractions import Fraction as F
import sympy as S

checks=0
P=S.symbols('P',integer=True,positive=True)
T=S.symbols('T')
assert S.expand((P-T)**3).coeff(T,2)==3*P
assert S.expand(P**3+3*P*(P/4))==P**3+S.Rational(3,4)*P**2
checks+=2
for L in (2,3,4):
    edges={};masks={};next_bit=0
    for site in product(range(L),repeat=4):
        for a,b in combinations(range(4),2):
            def step(x,k):
                y=list(x);y[k]=(y[k]+1)%L
                return tuple(y)
            boundary=((site,a),(step(site,a),b),
                      (step(site,b),a),(site,b))
            assert len(set(boundary))==4
            mask=0
            for edge in boundary:
                if edge not in edges:
                    edges[edge]=next_bit;next_bit+=1
                mask ^= 1<<edges[edge]
            assert mask not in masks
            masks[mask]=(site,a,b)
            checks+=2
    p=6*L**4
    assert len(masks)==p and len(edges)==4*L**4
    checks+=2
    signatures=list(masks)
    pairs=0
    for i,a in enumerate(signatures):
        for b in signatures[i+1:]:
            assert a^b not in masks
            pairs+=1
            checks+=1
    assert pairs==p*(p-1)//2
    checks+=1
    second=p*p+F(p,4)
    third=p**3+F(3*p*p,4)
    beta=F(1,16*p)
    upper=1-beta*p+beta**2*second/2
    lower=upper-beta**3*third/6
    assert 0<lower<=upper<1
    checks+=1
    print(f"L={L} bonds={4*L**4} plaquettes={p} E[D³]={third}")
    print(f" beta={beta}; T3<=Z<=T2: [{lower}, {upper}], width={upper-lower}")
print(f"ORIGINAL_WILSON_CUBIC_INCIDENCE_PASS={checks}")
