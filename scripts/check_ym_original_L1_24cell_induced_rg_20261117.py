#!/usr/bin/env python3
"""Induced ORIGINAL L1 Wilson finite RG effective rational coarse density.

24-cell is a finite rational SU2 subgroup. For all 24^4 original fine
links with six original commutator plaquettes, condition on the ACTUAL
noncommutative block B=U0*U1, and integrate out the three remaining
independent link variables (one conditional link + U2,U3).
The exact conditional moments are
  E[D|B]=19/4 - t,
  E[D²|B]=4*t²/3 - 169*t/18 + 230/9, t=(Re B)².
Hence the induced rational Taylor Gibbs density is a quadratic
polynomial in t. This is a genuine finite induced effective action
on the 24-element group, not an assumed same-beta Wilson action or
a full analytic exp-Haar RG theorem.
"""
from fractions import Fraction as Q
from itertools import product
from collections import defaultdict
from math import prod

V=[]
for a in range(4):
 for sign in (-1,1):
  q=[Q(0)]*4;q[a]=Q(sign);V.append(tuple(q))
for signs in product((-1,1),repeat=4):
 V.append(tuple(Q(s,2) for s in signs))
idx={q:i for i,q in enumerate(V)}
assert len(idx)==24
def mul(q,r):
 a,b,c,d=q;e,f,g,h=r
 return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
         a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
M=[[idx[mul(q,r)] for r in V] for q in V]
def deficit(i,j):
 q,r=V[i],V[j]
 return 2*sum((q[a]*r[b]-q[b]*r[a])**2
              for a,b in ((1,2),(1,3),(2,3)))
X=[[deficit(i,j) for j in range(24)] for i in range(24)]
cond=defaultdict(lambda:[0,Q(0),Q(0)])
for i,j,k,l in product(range(24),repeat=4):
 b=M[i][j]
 d=X[i][j]+X[i][k]+X[i][l]+X[j][k]+X[j][l]+X[k][l]
 cond[b][0]+=1
 cond[b][1]+=d
 cond[b][2]+=d*d
assert len(cond)==24
mu1=lambda t:Q(19,4)-t
mu2=lambda t:Q(4,3)*t*t-Q(169,18)*t+Q(230,9)
counts=defaultdict(int)
for b,(n,s1,s2) in cond.items():
 t=V[b][0]**2
 assert n==24**3
 assert s1/n==mu1(t)
 assert s2/n==mu2(t)
 counts[t]+=1
assert dict(counts)=={Q(0):6,Q(1,4):16,Q(1):2}
beta=Q(1,96)
def effective(t):
 return 1-beta*mu1(t)+beta*beta*mu2(t)/2
assert all(effective(t)>0 for t in counts)
Z=sum((n*effective(t) for t,n in counts.items()),Q(0))/24
assert Z==Q(140731,147456)
classes={Q(0):Q(78955,82944),
         Q(1,4):Q(422191,442368),
         Q(1):Q(35459,36864)}
assert all(effective(t)==w for t,w in classes.items())
# Exact pushforward measure and its conditional law.
coarse={b:effective(V[b][0]**2)/(24*Z) for b in range(24)}
assert sum(coarse.values(),Q(0))==1
assert all(coarse[b]>0 for b in coarse)
assert sum(coarse[b]*V[b][0] for b in coarse)==0
# The effective action is NOT just a renormalized Wilson plaquette
# constant: for three t values the exact conditional factors differ.
assert len(set(classes.values()))==3
for t in sorted(counts):
 print('t=',t,'class=',counts[t],'mu1=',mu1(t),
       'mu2=',mu2(t),'coarse relative weight=',effective(t))
print('Z=',Z)
print('YM_ORIGINAL_L1_INDUCED_RATIONAL_RG_PASS',
      24**4,'fine states, 24 conditional coarse fibres')
