#!/usr/bin/env python3
"""RH x native hyperfabric: true 27-graded C26/C13 signed codec commuting square.

Consumers: original P3^3 27-point cube, its projective Axis13+Bool codec,
Griess source grade order13 word; RH exact trace-preserving finite
projection/unfolding. Does not replace RH pi/3 physical witness.
Local finite and SymPy Q-matrix tests, NOT Agda or Lean kernel receipt.
"""
from itertools import product, combinations
from fractions import Fraction as F
import sympy as s

V=list(product((-1,0,1),repeat=3))
O=(0,0,0)
def mod3(x):return (x+1)%3-1
def M(p):
    x,y,z=p
    return tuple(map(mod3,(x+y,y+z,x+y+z)))
def A(p):return tuple(-t for t in p)
def G(p):return A(M(p))
def orient(p):
    for v in p:
        if v: return int(v<0)
    return None
def axis(p):return A(p) if orient(p)==1 else p
def encode(p):
    if p==O:return None
    return (axis(p),orient(p))
def decode(pair):
    a,b=pair
    return A(a) if b else a
def act(c): return encode(G(decode(c)))
def axisAct(a):return axis(M(a))
def cocycle(a):return orient(M(a))
def iterate(f,x,n):
    for _ in range(n):x=f(x)
    return x

nonzero=[x for x in V if x!=O]
axes=sorted({axis(p) for p in nonzero})
codes=[(a,b) for a in axes for b in (0,1)]
assert (len(V),len(nonzero),len(axes),len(codes))==(27,26,13,26)
assert all(decode(encode(p))==p for p in nonzero)
assert all(encode(decode(c))==c for c in codes)
assert all(decode(act(c))==G(decode(c)) for c in codes)
assert all(act((a,b))==(axisAct(a),b^cocycle(a)^1)
           for a in axes for b in (0,1))
assert sum(cocycle(a) for a in axes)==4
assert all(iterate(act,c,13)==(c[0],c[1]^1)
           and iterate(act,c,26)==c for c in codes)
assert iterate(M,(1,0,0),13)==(1,0,0)
assert len({iterate(G,(1,0,0),n) for n in range(26)})==26
assert all(iterate(G,p,13)==A(p) for p in nonzero)

# Original RH raw four-source history remains BOTH coordinates even
# when its observed pi/3 column cancels; coefficient signs are not erased.
source=(3,24,24,4,1)  # c, raw third left, raw third right, inner, outer
def project(src):
    c,l,r,inner,outer=src
    assert l==r
    return (src,(c,inner,outer))
def unfold(traced):
    src,(c,inner,outer)=traced
    return (src,(outer,inner,2*c,inner,outer))
def direct(src):
    c,l,r,inner,outer=src
    assert l==r
    return (src,(outer,inner,2*c,inner,outer))
def op_code(c):return act(c)
def x0(state):c,src=state;return (c,project(src))
def y0(state):c,src=state;return (c,direct(src))
def y10(state):c,tr=state;return (c,unfold(tr))
def x10(state):return state
def z(state):c,payload=state;return (op_code(c),payload)
# genuine all six H05 faces, bottom/top x-y plus nonidentity z:
for c in codes:
    x=(c,source)
    assert y10(x0(x))==x10(y0(x))          # xy0
    assert z(x0(x))==x0(z(x))              # xz0
    assert z(y0(x))==y0(z(x))              # yz0
    assert y10(x0(z(x)))==x10(y0(z(x)))   # xy1
    assert z(x10(y0(x)))==x10(z(y0(x)))   # xz1
    assert z(y10(x0(x)))==y10(z(x0(x)))   # yz1
    assert y10(x0(x))[1][0]==source       # raw four-site recovery
    assert z(x)[1]==source
    assert z(z(x))[1]==source
assert project((3,24,24,4,1))[1] == project((3,48,48,4,1))[1]
assert project((3,24,24,4,1))[0] != project((3,48,48,4,1))[0]

# Exact field geometry: the original Griess matrix G=-M over F3 is a
# primitive degree-three multiplication operator. This identifies, after
# choosing a cyclic basis, original F3^3 with GF(27), NOT with the
# NONWRAPPING spatial path-graph metric.
X=s.symbols("X")
matM=s.Matrix([[1,1,0],[0,1,1],[1,1,1]])
matG=-matM
f=s.Poly(matG.charpoly(X).as_expr(),X,modulus=3)
assert f==s.Poly(X**3-X+1,X,modulus=3)
assert all(f.eval(i)!=0 for i in (0,1,2))  # cubic irreducible
assert (matG**3-matG+s.eye(3)).applyfunc(lambda x:x%3)==s.zeros(3)
assert (matG**13+s.eye(3)).applyfunc(lambda x:x%3)==s.zeros(3)
assert (matG**26-s.eye(3)).applyfunc(lambda x:x%3)==s.zeros(3)
v=s.Matrix([1,0,0])
cyclic_basis=s.Matrix.hstack(v,matG*v,matG**2*v)
assert cyclic_basis.det()%3==1
# The cyclic G-action is multiplication by a primitive element of
# F_3[X]/(X^3-X+1) after this explicit basis change.
assert 26==2*13 and 27==1+2*13

# Correct source representation-theoretic split; no scalar phase
# is substituted for source sign or for the C2 orientation residual.
order=nonzero
index={v:i for i,v in enumerate(order)}
n=len(order);I=s.eye(n)
def permutation(f):
    m=s.zeros(n)
    for p in order:m[index[f(p)],index[p]]=1
    return m
PG,PA=permutation(G),permutation(A)
assert PG**13==PA and PG**26==I
E=(I+PA)/2;Odd=(I-PA)/2
assert E*E==E and Odd*Odd==Odd and E*Odd==s.zeros(n)
assert E+Odd==I and PG*E==E*PG and PG*Odd==Odd*PG
assert s.trace(E)==13 and s.trace(Odd)==13
assert s.trace(PG*E)==0 and s.trace(PG*Odd)==0
# G^13 is +I on the antipodal-even 13D sector, and -I on the
# anti-antipodal 13D sector, NOT a zeroed/forgotten orientation.
assert PG**13*E==E and PG**13*Odd==-Odd

def native_edge(a,b):
    return sum(x!=y for x,y in zip(a,b))==1 and all(
        x==y or x==0 or y==0 for x,y in zip(a,b))
edges=[(a,b) for a,b in combinations(V,2) if native_edge(a,b)]
assert len(edges)==54
assert sum(native_edge(G(a),G(b)) for a,b in edges)==0

print("PASS 26/26 exact original grade <-> 13-axis+orientation codec")
print("PASS 26/26 transported cocycle: 4 canonical sign flips, 9 no flips")
print("PASS 26/26 order13 antipodal flip and order26 return")
print("PASS 156/156 six-face nonidentity H05 finite tests, raw history preserved")
print("PASS irreducible GF(3) polynomial X^3-X+1, primitive GF(27)^x Singer C26")
print("PASS explicit cyclic field basis determinant 1 mod3 and 13/26 exact sequence")
print("PASS 26x26 rational even/odd antipodal projectors, 13+13 independent")
print("PASS 54/54 original spatial cube edges NOT preserved")
print("OPEN source-specific RH FarExact/compensation, true nine-DOF / physical equivariance")
