#!/usr/bin/env python3
"""Full L4 1536-plaquette Wilson action: exact source-first R445 fine two-mark fibre BIDI.

15 center-SU2 live links = 3 full native R445 axial pairs and 9 spectator links;
1009 other original links fixed I. Full continuous SU2 Haar and W3 not claimed.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations,product
from sympy import symbols,diff,log,simplify,Rational
L=4;O=(0,0,0,0)
def shift(x,j):
    y=list(x);y[j]=(y[j]+1)%L;return tuple(y)
def plaq(x,i,j):
    return ((x,i),(shift(x,i),j),(shift(x,j),i),(x,j))
plaquettes=[plaq(x,i,j) for x in product(range(L),repeat=4) for i,j in combinations(range(4),2)]
assert len(plaquettes)==1536
all_links={(x,j) for x in product(range(L),repeat=4) for j in range(4)}
def selected(a):
    x,j=a;return all(x[k]%2==0 for k in range(4) if k!=j)
all_selected={a for a in all_links if selected(a)}
assert len(all_links)==1024 and len(all_selected)==128 and len(all_links-all_selected)==896
all_pairs=[((x,j),(shift(x,j),j)) for j in range(4)
           for x in product(range(L),repeat=4)
           if x[j]%2==0 and all(x[k]%2==0 for k in range(4) if k!=j)]
assert len(all_pairs)==64 and set(sum((list(q) for q in all_pairs),[]))==all_selected
cube=[]
for i,j in combinations(range(3),2):
    k=next(iter({0,1,2}-{i,j}))
    cube.extend((plaq(O,i,j),plaq(shift(O,k),i,j)))
cube_links=set(sum((list(face) for face in cube),[]))
pairs=[((O,j),(shift(O,j),j)) for j in range(3)]
spectators=sorted(a for a in cube_links if not selected(a))
assert len(cube_links)==12 and len(spectators)==9 and all(p in all_pairs for p in pairs)
active=tuple(sorted(set(sum((list(pair) for pair in pairs),[])+spectators)))
assert len(active)==15 and len(all_links-set(active))==1009
ix={a:i for i,a in enumerate(active)}
mark_masks=[sum(1<<ix[a] for a in cube[j]) for j in (0,1)]
assert not mark_masks[0]&mark_masks[1]
affected=[sum(1<<ix[a] for a in face if a in ix) for face in plaquettes]
affected=[m for m in affected if m]
assert len(affected)==66
def weight(b):return Q(1,4**sum(((b&m).bit_count()&1) for m in affected))
def sign(b,m):return -1 if (b&m).bit_count()&1 else 1
def coarse(b):
    return sum(((((b>>ix[a])^(b>>ix[c]))&1)<<j) for j,(a,c) in enumerate(pairs))
def decode(w,f,sp):
    bits=0
    for j,(a,c) in enumerate(pairs):
        v=(f>>j)&1
        bits|=v<<ix[c];bits|=(v^((w>>j)&1))<<ix[a]
    for j,a in enumerate(spectators):bits|=((sp>>j)&1)<<ix[a]
    return bits
def columns(b):
    v=weight(b);f,g=[sign(b,m) for m in mark_masks]
    return (v,v*f,v*g,v*f*g)
K={}
for w in range(8):
    row=[Q(0)]*4
    for f in range(8):
        for sp in range(512):
            b=decode(w,f,sp)
            assert coarse(b)==w
            for j,x in enumerate(columns(b)):row[j]+=x
    K[w]=tuple(x/Q(4096) for x in row)
direct=defaultdict(lambda:[Q(0)]*4)
for b in range(32768):
    row=direct[coarse(b)]
    for j,x in enumerate(columns(b)):row[j]+=x
for w in range(8):
    assert K[w]==tuple(x/Q(4096) for x in direct[w])
    assert K[w][0]>0
Z,ZF,ZG,ZFG=(sum(K[w][j] for w in range(8))/8 for j in range(4))
assert (Z,ZF,ZG,ZFG)==tuple(sum(direct[w][j] for w in range(8))/Q(32768) for j in range(4))
c={w:K[w][3]-K[w][1]*K[w][2]/K[w][0] for w in range(8)}
assert all(c[w]!=0 for w in range(8))
cov=ZFG/Z-ZF*ZG/Z**2
cov_coarse=sum(K[w][1]*K[w][2]/K[w][0] for w in range(8))/8/Z-ZF*ZG/Z**2
cov_fibre=sum(c.values())/8/Z
assert cov==cov_coarse+cov_fibre
wrong=sum(K[w][1]*K[w][2]/K[w][0] for w in range(8))/8
assert wrong!=ZFG
# The pre-existing coarse-ONLY F19 two-mark theorem is exact: its fibre C is zero.
for w in range(8):
    f=(-1 if w&1 else 1);g=(-1 if w&2 else 1);k=K[w][0]
    assert (k*f*g)*k==(k*f)*(k*g)
s,t=symbols('s t')
full=Z+s*ZF+t*ZG+s*t*ZFG
push=sum(K[w][0]+s*K[w][1]+t*K[w][2]+s*t*K[w][3] for w in range(8))/8
assert simplify(full-push)==0
assert simplify(diff(log(full),s,t).subs({s:0,t:0})-Rational(cov.numerator,cov.denominator))==0
bad=Z+s*ZF+t*ZG+s*t*wrong
assert simplify(diff(log(bad),s,t).subs({s:0,t:0})-Rational(cov.numerator,cov.denominator))!=0
print('PASS original 1024 links, 128 selected / 896 spectator, 64 two-link R445 pairs; 1536 Wilson plaquettes / 66 affected')
print('PASS 32768 original fine and 32768 R445 reparameterized exact independent configurations')
print('PASS 8/8 full fine-gauge source four coefficients Z,F,G,FG and affine log mixed jet')
print('PASS 8/8 nonzero fine-fibre conditional covariances and coarse-only zero controls')
print('FAILS AS REQUIRED: independently averaged fine marks erase a real mixed st term')
print('FULL covariance',float(cov),'coarse conditional means',float(cov_coarse),'inside fibre',float(cov_fibre))
print('Fraction of connected response in original fibres',float(cov_fibre/cov))
print('SCOPE: exact finite SU2 center subgroup conditional slice, NOT full SU2 Haar, W3, Agda kernel or Clay')
