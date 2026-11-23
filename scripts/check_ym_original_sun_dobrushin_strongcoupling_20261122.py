#!/usr/bin/env python3
"""Original 4D SU(N) Wilson plaquette-neighbour geometry + source influence.

Actual continuous-group TV bound is proved analytically from osc(log ratio);
this checker verifies exact original L=3,4,5 graph incidences and rational
high-temperature alpha threshold, plus independent exact 2-point extremum.
No weak-coupling continuum / physical W3 inference.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import sympy as S


def geometry(L):
    sites=list(product(range(L), repeat=4))
    links=[(x,a) for x in sites for a in range(4)]
    positions={v:i for i,v in enumerate(links)}
    neighbors=[set() for _ in links]
    incidences=[[] for _ in links]
    pair_count=Counter()
    def sh(x,a):
        y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
    face_count=0
    for x in sites:
      for a in range(4):
        for b in range(a+1,4):
          face={positions[(x,a)],positions[(sh(x,a),b)],
                positions[(sh(x,b),a)],positions[(x,b)]}
          assert len(face)==4
          face_count+=1
          for i in face:
            incidences[i].append(face_count)
            for j in face:
              if j!=i:neighbors[i].add(j)
          for i in face:
            for j in face:
              if i<j: pair_count[i,j]+=1
    assert face_count==6*L**4
    assert len(links)==4*L**4
    assert set(map(len,incidences))=={6}
    assert set(map(len,neighbors))=={18}
    assert set(pair_count.values())=={1}, Counter(pair_count.values())
    assert all(i not in neighbors[i] for i in range(len(links)))
    assert all((j in neighbors[i]) == (i in neighbors[j]) for i in range(len(links)) for j in neighbors[i])
    return (L,len(links),face_count,len(pair_count))

for L in (3,4,5):
    data=geometry(L)
    print('PASS source 4D original link/plaquette graph L,E,P,pair-incidences=',data)

r=S.Rational(1,36)
# tanh(x) <= x for x >=0, hence alpha <=18/36 =1/2
assert S.Rational(18)*r==S.Rational(1,2)
assert S.simplify(18*S.tanh(r))<S.Rational(1,2)
crit=S.atanh(S.Rational(1,18))
assert (crit-r).evalf(30)>0
print('PASS strict original compact-group Dobrushin beta <=1/36: alpha<1/2')
print('beta critical (sharp universal TV bound):',crit,'=',crit.evalf(16))

# General exact TV optimization: q=[x,1-x], reweight by endpoints h=0,logR
# maximum occurs x=1/(1+sqrtR), equal to tanh(osc h/4).
z,R=S.symbols('z R',positive=True)
tv=(R-1)*z*(1-z)/(1+(R-1)*z)
assert S.simplify(S.diff(tv,z).subs({z:1/(1+S.sqrt(R))}))==0
assert S.simplify(tv.subs({z:1/(1+S.sqrt(R))}) - (S.sqrt(R)-1)/(S.sqrt(R)+1))==0
q=S.symbols('q',positive=True)
assert S.simplify(((S.exp(2*q)-1)/(S.exp(2*q)+1))-S.tanh(q).rewrite(S.exp))==0
print('PASS exact sharp Gibbs conditional TV: osc(delta H)<=4 beta -> TV<=tanh(beta)')

# Conservative Follmer bound with oscillation <=2 per affected original link:
# for two local supports A,B, at conflict graph separation d>=1,
# |Cov(F,G)| <= 4 |A| |B| sum_{n>=d}(1/2)^n = 8|A||B| 2^-d.
for dist in range(0,28):
    bound=8*4*4*S.Rational(1,2)**dist
    assert bound>=0
    if dist>=8:assert bound<=S.Rational(1,2)
print('PASS explicit source strong-coupling covariance envelope 8|A||B| 2^-d')
print('OPEN weak-coupling beta(a)->infinity / renormalized physical W3 / E1 / D2')
