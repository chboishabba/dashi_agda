#!/usr/bin/env python3
"""RH original atomic angular C4 vs hyperfabric C3 and source grammar cut.

Uses original sources: RH high-pole -20/351 discrete biharmonic,
ShiftPhaseTableInterference.Phase4, FiniteThreeCycleTorusExact.Residue3,
check_hyperfabric_path27_quantum_walk.py U(pi), and SOURCE-WRITTEN
LacanFrege/IrigarayLabial TernaryRoleCode directed edges.
Integer-q CRT is an exact selected finite SOURCE-CONSUMER comparison;
NOT actual zeta zeros or the real-q Fourier domain.
"""
from itertools import permutations
from collections import Counter
import sympy as s
Q=s.Rational
I3,I4,I12=s.eye(3),s.eye(4),s.eye(12)
T3,T4=s.zeros(3),s.zeros(4)
for j in range(3):T3[(j+1)%3,j]=1
for j in range(4):T4[(j+1)%4,j]=1
Z=s.kronecker_product(T3,T4)
S3=s.kronecker_product(T3,I4)
S4=s.kronecker_product(I3,T4)
assert Z**12==I12 and Z**4==S3 and Z**9==S4 and Z**3==S4.T
P4=-Q(20,351)*(S4+S4.T-2*I12)**2
B3=Q(2,3)*s.ones(3)-I3
W=s.kronecker_product(B3,I4)
assert P4==-Q(20,351)*(Z**3+(Z.T)**3-2*I12)**2
assert P4*W==W*P4 and W**2==I12
assert P4.rank()==9
assert P4.eigenvals()=={Q(0):3,-Q(80,351):6,-Q(320,351):3}
E4=s.kronecker_product(I3,(I4+T4+T4**2+T4**3)/4)
assert P4*E4==s.zeros(12) and E4.rank()==3
assert ((I12+W)/2*E4).rank()==1
assert ((I12-W)/2*E4).rank()==2
def F(q):return s.trigsimp(-Q(320,351)*s.sin(s.pi*q/4)**4)
def native(q):return 1 if q%3==0 else -1
pair={}
for q in range(12):
    z=(q%3,q%4)
    assert z not in pair
    pair[z]=q
    assert (4*(q%3)+9*(q%4))%12==q
    assert F(q+12)==F(q) and native(q+12)==native(q)
    assert F(q)==(Q(0),-Q(80,351),-Q(320,351),-Q(80,351))[q%4]
assert len(pair)==12
assert (1%3)==(4%3) and F(1)==-Q(80,351) and F(4)==0
assert (0%3)==(3%3) and F(0)==0 and F(3)==-Q(80,351)
assert native(1)==native(4)==-1
assert Counter((F(q),native(q)) for q in range(12))=={
 (Q(0),1):1,(Q(0),-1):2,(-Q(80,351),1):2,
 (-Q(80,351),-1):4,(-Q(320,351),1):1,
 (-Q(320,351),-1):2}
# Original finite Lacan comparison graph: code1->0 and code1->2.
# Original Irigaray contact: code1<->code2; code0 isolated.
lacan={(1,0),(1,2)}
iri={(1,2),(2,1)}
assert all({(p[a],p[b]) for a,b in lacan}!=iri
           for p in permutations(range(3)))
ssp=(-1,0,1)
lc={0:-1,1:0,2:1};ic={0:0,1:-1,2:1}
def lap(edges,chart):
    A=s.zeros(3)
    for a,b in edges:
        x=ssp.index(chart[a]);y=ssp.index(chart[b])
        A[x,y]=A[y,x]=1
    return s.diag(*[sum(A[i,j] for j in range(3)) for i in range(3)])-A
Lp=lap(lacan,lc);Li=lap(iri,ic)
Lc=3*I3-s.ones(3)
assert Lp.eigenvals()=={0:1,1:1,3:1}
assert Li.eigenvals()=={0:2,2:1}
assert Lc.eigenvals()=={0:1,3:2}
assert Li*(Li-2*I3)==s.zeros(3)
assert Lp!=Li and Li!=Lc and Lp!=Lc
assert B3!=I3 and (B3-I3).rank()==2
print("PASS RH original -20/351 C4 biharmonic, C12 joint time+angular rank9 kernel3")
print("PASS kernel 1 native positive / 2 native negative; genuine q4 notch negative time phase")
print("PASS C3-only RH non-descent, 12/12 exact CRT integer-frequency recovery")
print("PASS actual directed Lacan/Irigaray grammar no six-permutation equivalence")
print("PASS source symmetrized Lacan P3 U(pi)=B, Irigaray K2+isolated U(pi)=I")
print("OPEN real-q analytic, selected smooth W, actual zeros/mu/FarExact and A2 terminal")
