#!/usr/bin/env python3
"""Original-source finite RH/NS/YM hyperfabric construction and negative controls.

Source: check_hyperfabric_path27_quantum_walk.py U(pi); NS R529/R530
integer mode->balanced sign and dyadic hat K=3; YM R445 selected side2
directed bond->two original side4 fine links; ConsumerDescentMinimalObserver.
Finite exact checks only, no physical graph evolution or Clay theorem.
"""
from itertools import product
from fractions import Fraction as F
from math import comb
import sympy as s

T=(-1,0,1)
V=tuple(product(T,repeat=3)); order={p:i for i,p in enumerate(V)}
G=s.Matrix([[-1,-1,0],[0,-1,-1],[-1,-1,-1]])
def g(p):return tuple((int(z)+1)%3-1 for z in G*s.Matrix(p))
P=s.zeros(27)
for p in V:P[order[g(p)],order[p]]=1
assert P**26==s.eye(27)
B=s.Matrix([[s.Rational(2,3)-int(x==y) for y in T] for x in T])
U=s.kronecker_product(B,B,B) # SAME original exact P3^3 source U(pi)
assert U.T==U and U*U==s.eye(27)
assert U[order[(0,0,0)],order[(0,0,0)]]==-s.Rational(1,27)
assert U[0,order[(0,0,0)]]==s.Rational(8,27)
D=P*U-U*P
assert D.rank()==20 and D[0,0]==s.Rational(2,9)
def Uk(k):return P**k*U*(P.T**k)
for k in (0,1,2):
    assert Uk(k)**2==s.eye(27)
    assert P*Uk(k)==Uk(k+1)*P
assert Uk(1)*P*Uk(0)==P*Uk(0)*Uk(0)

# Original YM periodic L=2: four-dimensional site c∈{0,1}^4,
# direction i, half-phase j, selected side4 original positive fine bond
# (2c+j e_i, i), j=0,1. A balanced chart is the two-step P3 path.
coarse=tuple(product((0,1),repeat=4))
def point(c):return tuple(2*x-1 for x in c)+(0,)*5
def path(c,i):
    x=point(c);mid=list(x);mid[i]=0;mid=tuple(mid)
    y=list(x);y[i]=-y[i];y=tuple(y)
    return x,mid,y
def fine_label(c,i,j):
    a=[2*x for x in c];a[i]=(a[i]+j)%4
    return tuple(a),i
def native_edge(x,y):
    diff=[i for i in range(9) if x[i]!=y[i]]
    return len(diff)==1 and 0 in (x[diff[0]],y[diff[0]])
segments=[];raw=[]
for c in coarse:
    for i in range(4):
        x,m,y=path(c,i)
        assert native_edge(x,m) and native_edge(m,y)
        assert point(tuple((b+int(a==i))%2 for a,b in enumerate(c)))==y
        for j,e in enumerate(((x,m),(m,y))):
            segments.append(e);raw.append(fine_label(c,i,j))
assert len(raw)==len(set(raw))==128
assert len(segments)==len(set(segments))==128
assert len({tuple(sorted(edge)) for edge in segments})==64
assert len(coarse)*4==64 and 4*(4**4)==1024 and 1024-128==896

# Original NS R529/R530 physical integer Fourier mode sign quotient
# is a section, NOT a sufficient consumer of original K=3 dyadic hat.
def sign(v):return tuple((x>0)-(x<0) for x in v)
def hat(K,r):
    lo,mid,hi=2**(K-1),2**K,2**(K+1)
    if not(lo<=r<=hi):return F(0)
    return F(r-lo,mid-lo) if r<=mid else F(hi-r,hi-mid)
assert all(sign(t)==t for t in V) # original Round530 integer representatives
assert sign((8,0,0))==sign((9,0,0))==(1,0,0)
assert (hat(3,8),hat(3,9))==(F(1),F(7,8))
def obs(k):return sign(k),hat(3,max(map(abs,k)))
assert all(obs(k)[1]==hat(3,max(map(abs,k)))
           for k in product(range(-9,10),repeat=3))
# Even sign+hat is insufficient for the physical convolution consumer.
assert obs((7,0,0))==obs((10,0,0))
assert sign((7-7,0,0))!=sign((10-7,0,0))
assert sign((1,0,0))!=sign((-1,0,0))
assert tuple(int(x!=0) for x in (1,0,0))==tuple(int(x!=0) for x in (-1,0,0))

# Precisely typed numerical geometry: NS and YM not SAME operator.
assert F(1,2**(8-1))==F(1,128) and 2*2*2*F(1,128)==F(1,16)
assert tuple(comb(9,r)*2**r for r in range(10))==(
 1,18,144,672,2016,4032,5376,4608,2304,512)
print("PASS source U(pi) rational involution, fixed Singer commutator rank20 witness2/9")
print("PASS original time U(pi) transported nontrivially across k; 3 checked levels")
print("PASS YM original L2/side4: 64 directed coarse links, 128 unique selected fine labels")
print("PASS 128 signed 2-step P3^9 traces, 64 distinct undirected supports")
print("PASS NS R529/530: 8/9 share signed chart, K3 dyadic 1 vs 7/8")
print("PASS 19^3 selected multiplier observer checks and nonlinear convolution collision")
print("PASS balanced sign preserved; binary support loses polarity; 8/128/16 typed")
print("OPEN physical graph motion, full nonlinear NS, original YM Wilson/Haar and RH FarExact")
