#!/usr/bin/env python3
"""Faithful parity-even trinification H: exact fundamental-loop charge/deck audit.

Physical H = (SU(3)c x U(2)L x U(2)R) / Z3_diag, with U(2)
realized as S(U(2)xU(1)) in each SU(3). Original source E6/27 and
Chi33 action: dashi_agda #1106; orbifold quotient/clutch: #1241.
Classical original mathematics: covering homotopy exact sequence and
clutching classification of complex lines; this source-specific integer
presentation is a Johl Brown / ChatGPT-assisted computation.

A,B are the original cover U(2)L/U(2)R determinant-one winding loops;
C is the common p=1 central-endpoint loop. Three copies of C have
U(2) determinant winding 2 in EACH factor (SU3c has pi1=0), hence
3 C = 2 A + 2 B. The resulting abelian pi1(H) has NO torsion:
with R=C-A-B as a second generator, B=-A-3R and C=-2R.
The Chi33 associated line character evaluates A->-1, B->+1,
C->0; in coordinates (A,R) it is -A. The deck class is R mod3.
Thus Chi degree and Z3 lifting obstruction are INDEPENDENT inputs.
This is topology, not a five-dimensional APS/eta/CS/WZ functional.
"""
from itertools import product
from fractions import Fraction
from math import gcd

# Ordered coordinate pair in the free abelian group <A,R> = Z^2.
A=(1,0)
R=(0,1)
B=(-1,-3)
C=(0,-2)
def add(x,y): return x[0]+y[0],x[1]+y[1]
def scale(k,x): return k*x[0],k*x[1]
def neg(x): return scale(-1,x)
assert scale(3,C)==add(scale(2,A),scale(2,B))
assert R==add(C,add(neg(A),neg(B)))
assert B==add(neg(A),scale(-3,R))
assert C==scale(-2,R)
# These 2x2 minors have gcd 1, so A,B,C span the whole Z^2.
dets=lambda u,v:u[0]*v[1]-u[1]*v[0]
assert gcd(gcd(abs(dets(A,B)),abs(dets(A,C))),abs(dets(B,C)))==1
assert dets(A,R)==1

# Explicit quotient-loop homotopy map and inverse on the selected torus.
# p is the common diagonal-Z3 endpoint exponent. mL,mR are determinant
# winding increments in the two U2 blocks (the independent m,n choices
# in the original full torus only enter through their sum).
def coordinates(p, dL, dR):
    assert p in (0,1,2)
    return (dL-dR, -3*dR-2*p)
def representative(x,y):
    p=y%3
    dR=(-y-2*p)//3
    assert -y-2*p==3*dR
    dL=x+dR
    return p,dL,dR

def deck(loop): return loop[1]%3
def chi_degree(loop): return -loop[0]

for x,y in product(range(-14,15),repeat=2):
    assert coordinates(*representative(x,y))==(x,y)
    assert chi_degree((x,y))==-x
    assert deck((x,y))==y%3
for p,dL,dR in product(range(3),range(-8,9),range(-8,9)):
    z=coordinates(p,dL,dR)
    assert deck(z)==p
    assert chi_degree(z)==dR-dL
    assert coordinates(*representative(*z))==z
# Counterexample: one unchanging deck p=1 and arbitrary first Chern
# number; also unchanged Chi c1=0 with all three deck values.
for p,k in product(range(3),range(-30,31)):
    z=coordinates(p,0,k)
    assert (deck(z),chi_degree(z))==(p,k)
for p in range(3):
    assert (deck(coordinates(p,0,0)),chi_degree(coordinates(p,0,0)))==(p,0)
# p=1 has infinite order in pi1(H), although its DECK IMAGE is order 3.
assert all(scale(k,C)!=(0,0) for k in range(1,50))
assert deck(C)==1 and deck(scale(3,C))==0 and scale(3,C)!=(0,0)

# Exact Pickover 9999! projection on the unrelated finite circle,
# source PR #1260; this is an observer with a 99-element kernel.
N=9999
power=4950
assert pow(power,2,N)==power
assert gcd(power,N)==99
assert {(power*j)%N for j in (0,N//3,2*N//3)}=={0}
# There is no faithful map from the infinite Z^2 pi1(H) to finite mu9999.
# In particular, projection of the Z3 *DECK QUOTIENT* onto the
# mu3 subgroup then through the source Pickover power forgets deck p.
assert len({(power*(p*(N//3)))%N for p in range(3)})==1
print('PASS pi1(H) lattice generators: 3C=2A+2B, A,R free basis (rank 2; no torsion)')
print('PASS exact loop↔Z² inverse 841 integer pairs and 867 selected triple loops')
print('PASS character Chi33=-A, deck=R mod 3; both independent and realizable')
print('PASS a p=1 quotient loop has infinite order, although its Z3 deck image does not')
print('PASS finite Pickover mu9999 power loses chosen deck embedding, not original line data')
print('OPEN physical spin quotient eta/CS/WZ and defect-complete Higgs action')
