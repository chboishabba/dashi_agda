#!/usr/bin/env python3
"""YM P0: original global 1/F/G/FG source and bad-contour response comparison.

Exact Fraction test on original 4D L=4 1536-Wilson-action centre-valued
SU(2) subgroup slice (NOT full continuous-Haar SU(2) integration).
The abstract comparison lemma holds for any true positive original SU(N)
Wilson probability and |F|,|G|<=1; its proof is analytic, not enumeration.
"""
from fractions import Fraction as Q
from collections import Counter
from itertools import combinations,product

L=4
sites=list(product(range(L),repeat=4))
def step(x,i):
 y=list(x);y[i]=(y[i]+1)%L;return tuple(y)
def edges(x,i,j):
 return ((x,i),(x,j),(step(x,j),i),(step(x,i),j))
faces=[(x,i,j) for x in sites for i,j in combinations(range(4),2)]
F=(0,0,0,0),1,2
G=(2,0,0,0),1,2
walls=[(t,0,0,0) for t in (0,1)]
T=[(x,0,1) for x in walls]+[(tuple([x[0],0,1,0]),0,1) for x in walls]+[(x,0,2) for x in walls]+[(tuple([x[0],1,0,0]),0,2) for x in walls]
H=(1,0,0,0),1,2
linksF=set(edges(*F));linksG=set(edges(*G));linksH=set(edges(*H))
active=sorted(linksF|linksG|linksH)
assert len(active)==12 and len(set(active))==12
which={e:i for i,e in enumerate(active)}
def mask(face):
 m=0
 for e in edges(*face):
  if e in which:m ^= 1<<which[e]
 return m
masks=Counter(mask(f) for f in faces)
assert len(faces)==1536 and sum(masks.values())==1536
maskF=mask(F);maskG=mask(G)
root=sorted(linksF)[0]
nearRoot=[mask(f) for f in faces if root in edges(*f)]
assert len(nearRoot)==6

def sign(bits,m):return 1-2*((bits&m).bit_count()%2)
records=[]
for bits in range(1<<len(active)):
 bad=sum(mult for ma,mult in masks.items() if ma and sign(bits,ma)==-1)
 Fv=sign(bits,maskF);Gv=sign(bits,maskG)
 event=any(sign(bits,ma)==-1 for ma in nearRoot)
 records.append((bad,Fv,Gv,event))
max_bad=max(r[0] for r in records)
# Exactly original Wilson exp(-beta sum d_p), beta=ln2, d_p=0 or2:
# integer rescaling 4^(max_bad-bad), constant cancels in normalized law.
original=[(4**(max_bad-bad),f,g,badflag) for bad,f,g,badflag in records]
tot=sum(v[0] for v in original)
removed=sum(v[0] for v in original if v[3])
p=Q(removed,tot)
assert 0<p<1
rho=Q(9,100)
C=6*(1+rho)**2/(1-rho)**4
assert C==Q(712860000,68574961)
checks=0

def assertTrue(condition):
 global checks
 assert condition
 checks+=1

# Source coefficients are single global insertion, never one copy per cluster.
def moments(only_good=False):
 xs=[v for v in original if not only_good or not v[3]]
 mass=sum(v[0] for v in xs)
 return tuple(Q(sum(v[0]*(v[1]**lf)*(v[2]**rg) for v in xs),mass)
              for lf,rg in ((0,0),(1,0),(0,1),(1,1)))
allmom=moments();goodmom=moments(True)
assertTrue(allmom[0]==goodmom[0]==1)
assertTrue(all(-1<=x<=1 for x in allmom[1:]+goodmom[1:]))

def response(mom,s,t):
 a,b,c,d=mom
 K=a+s*b+t*c+s*t*d
 Ks=b+t*d;Kt=c+s*d;Kst=d
 return Kst/K-Ks*Kt/(K*K)

def explicit_tilt(mom,s,t):
 # Via original four source moments, rather than independent per-polymer marks.
 a,b,c,d=mom
 K=a+s*b+t*c+s*t*d
 ef=(b+t*d)/K;eg=(c+s*d)/K;efg=d/K
 return efg-ef*eg

for s,t in product((-rho,-Q(3,100),Q(0),Q(3,100),rho),repeat=2):
    lhs=response(allmom,s,t);rhs=response(goodmom,s,t)
    assertTrue(lhs==explicit_tilt(allmom,s,t))
    assertTrue(rhs==explicit_tilt(goodmom,s,t))
    assertTrue(abs(lhs-rhs)<=C*p)
    # Actual tilted bad probability <= ((1+rho)/(1-rho))^2 * p.
    zfull=sum(w*(1+s*f)*(1+t*g) for w,f,g,_ in original)
    zbad=sum(w*(1+s*f)*(1+t*g) for w,f,g,flag in original if flag)
    ptilt=Q(zbad,zfull)
    assertTrue(0<=ptilt<=Q((1+rho)**2,(1-rho)**2)*p)

# Four-column identity at s=t=0 gives original covariance; the bad-domain
# difference bound is <=6p, stronger than the uniform bidisk C*p.
assertTrue(response(allmom,Q(0),Q(0))==allmom[3]-allmom[1]*allmom[2])
assertTrue(abs(response(allmom,Q(0),Q(0))-response(goodmom,Q(0),Q(0)))<=6*p)
print('PASS original L4 product (1024 links, 1536 plaquettes), 12-live-link centre SU2 SOURCE SLICE')
print('PASS 4096 fine assignments, 25 rational two-global-mark source settings,',checks,'exact rational comparisons')
print('Original centre-slice bad probability p=',float(p),' original covariance=',float(response(allmom,Q(0),Q(0))))
print('Sharp consistent coefficient C(9/100)=',C,'≈',float(C))
print('THIS IS NOT CONTINUOUS SU(N) HAAR, NOR A CMP119 ACTIVITY/ABSOLUTE W3 OR OS GAP.')
