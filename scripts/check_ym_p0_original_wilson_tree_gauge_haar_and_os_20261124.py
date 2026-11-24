#!/usr/bin/env python3
"""YM P0: source-faithful original Wilson maximal-tree Haar gauge reduction.

Proof scope: any finite connected oriented graph and any compact group with
normalized bi-invariant Haar, for GAUGE-INVARIANT integrable observables.
SU(2) Q8 is an exact noncommuting local regression, not continuous Haar itself.
The full original L4 Wilson action is used for the source geometry regression.
Also checks a separate *conditional* dense-core spectral argument; it does NOT
establish YM physical CMP119 gauge/FP, W3 decay, interacting continuum or gap.

Run with Python 3 and SymPy 1.14; no Agda, Lean, GitHub CI or network.
"""
from collections import deque
from fractions import Fraction as Q
from itertools import product, combinations
from random import Random
from math import comb
import sympy as s

one=(1,0,0,0)
Q8=tuple(tuple(sign*int(k==j) for k in range(4)) for j in range(4) for sign in (1,-1))
assert len(Q8)==8 and len(set(Q8))==8

def mul(p,q):
    a,b,c,d=p; e,f,g,h=q
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)

def inv(p):return (p[0],-p[1],-p[2],-p[3])
def prod(*xs):
    r=one
    for x in xs:r=mul(r,x)
    return r
assert all(mul(q,inv(q))==one and mul(inv(q),q)==one for q in Q8)
assert all(mul(p,q) in Q8 for p in Q8 for q in Q8)
assert mul(Q8[2],Q8[4])!=mul(Q8[4],Q8[2])
checks=dict(group=4,graph=0,rooted=0,source=0,F19=0,finite_haar=0,os=0)

L=4
vertices=list(product(range(L),repeat=4))
Vset=set(vertices)
def step(x,a):
    y=list(x);y[a]=(y[a]+1)%L;return tuple(y)
links=tuple((x,a) for x in vertices for a in range(4))
faces=tuple(((x,a),(step(x,a),b),(step(x,b),a),(x,b))
            for x in vertices for a,b in combinations(range(4),2))
assert len(vertices)==256 and len(links)==1024 and len(faces)==1536
adj={x:[] for x in vertices}
for e in links:
    x,a=e; y=step(x,a)
    adj[x].append((y,e,1))
    adj[y].append((x,e,-1))
root=(0,0,0,0)
parent={root:None};tree=[];order=[root];todo=deque([root])
while todo:
    x=todo.popleft()
    for y,e,orientation in adj[x]:
        if y not in parent:
            parent[y]=(x,e,orientation)
            tree.append(e)
            order.append(y);todo.append(y)
assert set(parent)==Vset and len(tree)==255 and len(set(tree))==255
Tset=set(tree)
off=tuple(e for e in links if e not in Tset)
assert len(off)==769 and len(off)+len(tree)==1024
checks['graph']+=5

def gauge(U,g):
    return {e:prod(g[e[0]],U[e],inv(g[step(e[0],e[1])])) for e in links}

def treefix(U):
    g={root:one}
    for y in order[1:]:
        x,e,sign=parent[y]
        g[y]=mul(g[x], U[e] if sign==1 else inv(U[e]))
    fixed=gauge(U,g)
    assert all(fixed[e]==one for e in tree)
    return fixed,g

def reconstruct(X,g):
    return {e:prod(inv(g[e[0]]),X[e],g[step(e[0],e[1])]) for e in links}

def hol(U,face):
    a,b,c,d=face
    return prod(U[a],U[b],inv(U[c]),inv(U[d]))

def deficit(U,face):return 1-hol(U,face)[0]

froot=(0,0,0,0);groot=(0,0,0,2)
def face_at(x,a,b):return ((x,a),(step(x,a),b),(step(x,b),a),(x,b))
original_F=face_at(froot,2,3);original_G=face_at(groot,2,3)
assert original_F in faces and original_G in faces and original_F!=original_G
def action_and_marks(U):
    return (sum(deficit(U,p) for p in faces),
            deficit(U,original_F),deficit(U,original_G))

pairs=[]
for c in product(range(2),repeat=4):
    x=tuple(2*v for v in c)
    for a in range(4):pairs.append(((x,a),(step(x,a),a)))
selected={e for pair in pairs for e in pair}
assert len(pairs)==64 and len(selected)==128 and len(set(links)-selected)==896
checks['graph']+=3

rng=Random(119122445)
for case in range(12):
    # Use full, honest original 1024-link coordinates: no change of the source
    # Wilson action, and all spectator links are present (most may be I).
    U={e:one for e in links}
    for e in rng.sample(links,90+case*5):U[e]=rng.choice(Q8)
    X,g=treefix(U)
    assert reconstruct(X,g)==U
    assert action_and_marks(X)==action_and_marks(U)
    checks['rooted']+=3
    h={v:rng.choice(Q8) for v in vertices}
    Uh=gauge(U,h)
    Xh,gh=treefix(Uh)
    assert action_and_marks(Uh)==action_and_marks(U)
    assert all(Xh[e]==prod(h[root],X[e],inv(h[root])) for e in links)
    assert reconstruct(Xh,gh)==Uh
    checks['rooted']+=3
    for p in faces:
        assert hol(Uh,p)==prod(h[p[0][0]],hol(U,p),inv(h[p[0][0]]))
        checks['source']+=1
    for e0,e1 in pairs:
        u0,u1=U[e0],U[e1]
        w=mul(u0,u1);v=u1
        start=e0[0];end=step(e1[0],e1[1]);mid=e1[0]
        assert mul(w,inv(v))==u0
        assert mul(Uh[e0],Uh[e1])==prod(h[start],w,inv(h[end]))
        assert Uh[e1]==prod(h[mid],v,inv(h[end]))
        assert mul(mul(Uh[e0],Uh[e1]),inv(Uh[e1]))==Uh[e0]
        checks['F19']+=4

# Exhaustive exact noncommutative finite-group HAAR check on the small connected
# 3-vertex, 4-edge double-loop graph with nontrivial *shared* Wilson action.
# A general compact-group mathematical result is NOT derived by extrapolating Q8.
q=Q(1,2)

def small_fine(e0,e1,e2,e3):
    l1=prod(e0,e1,e2)
    l2=prod(e0,e1,inv(e3))
    l3=mul(l1,inv(l2))
    F=1-l1[0]; G=1-l2[0]
    w=q**(F+G+(1-l3[0]))
    return (w,w*F,w*G,w*F*G)

def add(x,y):return tuple(a+b for a,b in zip(x,y))
Z=(Q(0),)*4
full=Z
for e0,e1,e2,e3 in product(Q8,repeat=4):
    full=add(full,small_fine(e0,e1,e2,e3));checks['finite_haar']+=1
reduced=Z
for e2,e3 in product(Q8,repeat=2):
    reduced=add(reduced,small_fine(one,one,e2,e3));checks['finite_haar']+=1
assert tuple(v/Q(8**4) for v in full)==tuple(v/Q(8**2) for v in reduced)
checks['finite_haar']+=4
assert reduced[0]>0 and reduced[3]*reduced[0]-reduced[1]*reduced[2]!=0
checks['finite_haar']+=2

# Same-H dense-core implication (a logical consumer, not Wilson spectral data):
# If for every vector in a DENSE centered subspace of one positive OS H,
# <v,e^-tH v> <= C_v e^-mt for all t, then spectral projection below m
# is zero by positivity of diagonal spectral measures and density.
# Matrix tests distinguish selected/non-dense vs complete/dense controls.
t=s.symbols('t',nonnegative=True)
H=s.diag(0,s.Rational(1,3),s.Rational(2,3))
T=s.diag(1,s.exp(-t/s.Integer(3)),s.exp(-2*t/s.Integer(3)))
Omega=s.Matrix([1,0,0]);vfast=s.Matrix([0,0,1]);vslow=s.Matrix([0,1,0])
assert (vfast.T*T*vfast)[0]==s.exp(-2*t/3)
assert (vslow.T*T*vslow)[0]==s.exp(-t/3)
assert s.limit(s.exp(s.Rational(1,2)*t)*(vfast.T*T*vfast)[0],t,s.oo)==0
assert s.limit(s.exp(s.Rational(1,2)*t)*(vslow.T*T*vslow)[0],t,s.oo)==s.oo
assert s.Matrix.hstack(vfast,vslow).rank()==2
assert H[1,1]<s.Rational(1,2)<H[2,2]
checks['os']+=6
print('PASS SymPy',s.__version__,sum(checks.values()),checks)
print('ORIGINAL L4 full 1024/1536 action: 255 rooted tree, 769 off-tree, 64 R445 pairs and 896 spectators')
print('12 noncommuting Q8 original Wilson fields: gauge action, 1536 native face words, rooted inverse and covariance')
print('exhaustive Q8 3-vertex double-loop: 4096/4096 full configurations vs 64/64 tree-fixed quotient; 1/F/G/FG exact')
print('SPECTRAL: positivity+dense local core implication is conditional, separate from physical Yang-Mills')
print('OPEN: literal Balaban background FP/R/Q_B CMP119/122 T, ALL original W3 absolute shells, physical R4 same-H OS')
