#!/usr/bin/env python3
"""Original 4D Wilson side-four local continuous SU2 Haar six-face tube moment.

This finite local source test is NOT an all-beta, cutoff-uniform continuum gap.
Full original Wilson source has 1024 fine positive links/1536 plaquettes.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import numpy as np
import opt_einsum as oe
import sympy as S

L=4
def shift(site,axis):
    out=list(site);out[axis]=(out[axis]+1)%L;return tuple(out)
def plaquette(site,a,b):
    assert a<b
    return ((site,a,1),(shift(site,a),b,1),(shift(site,b),a,-1),(site,b,-1))
links=[(site,ax) for site in product(range(L),repeat=4) for ax in range(4)]
idx={e:i for i,e in enumerate(links)}
plaquettes=[(site,a,b,plaquette(site,a,b)) for site in product(range(L),repeat=4)
            for a in range(4) for b in range(a+1,4)]
assert len(links)==1024 and len(plaquettes)==1536

def mask(w):
    m=0
    for p,a,_ in w:m^=1<<idx[(p,a)]
    return m
assert len({mask(w) for _,_,_,w in plaquettes})==1536
o=(0,0,0,0)
F=plaquette(o,1,2)
G=plaquette(shift(o,0),1,2)
boundary={(p,a) for p,a,_ in F+G}
assert len(boundary)==8 and not {(p,a) for p,a,_ in F}&{(p,a) for p,a,_ in G}
faces=[]
for ax in range(3):
    a,b=[j for j in range(3) if j!=ax]
    for side in range(2):
        p=[0]*4;p[ax]=side
        faces.append((ax,side,plaquette(tuple(p),a,b)))
sides=[w for ax,side,w in faces if ax!=0]
assert len(sides)==4
from functools import reduce
assert reduce(int.__xor__,[mask(w) for w in sides],0)==mask(F)^mask(G)
incidence=Counter(len({(p,a) for p,a,_ in w}&boundary) for _,_,_,w in plaquettes)
assert incidence==Counter({0:1498,1:32,2:4,4:2})
assert {tuple(w) for _,_,_,w in plaquettes
        if len({(p,a) for p,a,_ in w}&boundary)==2}=={tuple(w) for w in sides}
assert all(len({(p,a) for p,a,_ in w}&{(p,a) for p,a,_ in F})<=1
           for _,_,_,w in plaquettes if w!=F)
assert all(len({(p,a) for p,a,_ in w}&{(p,a) for p,a,_ in G})<=1
           for _,_,_,w in plaquettes if w!=G)

def qmul(x,y):
    sx,ix=x;sy,iy=y;s=sx*sy
    if ix==0:return s,iy
    if iy==0:return s,ix
    if ix==iy:return -s,0
    pos={(1,2):3,(2,3):1,(3,1):2}
    if (ix,iy) in pos:return s,pos[(ix,iy)]
    return -s,{(2,1):3,(3,2):1,(1,3):2}[(ix,iy)]
def scalar_trace(indices,signs):
    a=(1,0)
    for k,sgn in zip(indices,signs):
        a=qmul(a,(-1 if k and sgn<0 else 1,k))
    return a[0] if a[1]==0 else 0

# Each cube edge appears twice in the six original oriented face words.
# Continuous SU2 Haar is uniform S3: E[q_i*q_j]=delta_ij/4.
used={}
contraction=[]
for _,_,face in faces:
    subs=''
    for p,a,sgn in face:
        if (p,a) not in used:used[(p,a)]='abcdefghijkl'[len(used)]
        subs+=used[(p,a)]
    T=np.empty((4,)*4,dtype=np.int64)
    signs=[sgn for _,_,sgn in face]
    for v in product(range(4),repeat=4):
        T[v]=scalar_trace(v,signs)
    contraction.extend((T,subs))
assert len(used)==12
assert Counter(''.join(contraction[i] for i in range(1,12,2)))==Counter({x:2 for x in 'abcdefghijkl'})
n=int(oe.contract(*contraction,[],optimize='optimal'))
assert n==16384 and Fraction(n,4**12)==Fraction(1,1024)

# Independent SU2 character a_d=I_(d-1)-I_(d+1)=2d I_d(beta)/beta.
# The isolated sphere's d=2 term produces beta**6/1024,
# whose TWO distinct face-coupling derivatives give beta**4/1024.
beta=S.symbols('beta')
a2=S.besseli(1,beta)-S.besseli(3,beta)
assert S.series(a2,beta,0,5).removeO().expand()==beta/2+beta**3/24
assert S.series(a2**6/16,beta,0,8).removeO().expand()==beta**6/1024
assert S.expand((S.Rational(1,2)**2)*(beta/2)**4/16)==beta**4/1024

print('PASS true original 1024 links, 1536 original plaquettes and masks')
print('PASS F/G nonoverlap and eight-edge incidence',dict(incidence))
print('PASS four unique side faces and 12-link 6-face double incidence')
print('PASS exact continuous SU2 Haar integer contraction',n,'/4^12 = 1/1024')
print('PASS independent SU2 character coefficient: local beta^4 / 1024')
print('NOT original cutoff-uniform weak-coupling beta(a), RG W3 or OS mass gap')
