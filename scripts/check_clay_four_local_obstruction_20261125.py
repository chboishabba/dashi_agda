"""Finite controls for the source arguments; not an actual Selmer/PDE/Chow run."""
from fractions import Fraction as Q
from itertools import permutations, product
from collections import defaultdict
import random
import sympy as S

def need(ok):
    if not ok: raise ArithmeticError('regression failed')

# RH: causal inverse to the original signed triangular consumer.
for q in range(1,10):
    step=Q(1,q)
    atoms=[(Q(2,7),Q(5,3)),(Q(7,6),Q(3,2)),(Q(8,3),Q(7,5))]
    A=lambda t:sum(w*max(t-a,0) for a,w in atoms)
    tent=lambda t:A(t+1)-2*A(t)+A(t-1)
    for j in range(-q,7*q):
        t=j*step
        need(sum(k*tent(t-k) for k in range(1,10))==A(t))
print('RH 360 exact causal triangular inverse controls')

# BSD: actual E:y^2+y=x^3, point (0,0), #E(F2)=3.
pts=[(x,y) for x,y in product(range(2),repeat=2) if (y*y+y-x**3)%2==0]
need(pts==[(0,0),(0,1)])
# Tangent y=0 intersects cubic triply at P, so [3]P=O.
x=S.symbols('x');need(S.expand(0**2+0-x**3)==-x**3)
G=[(a,b,c,d) for a,b,c,d in product(range(3),repeat=4) if (a*d-b*c)%3]
def mul(A,B):
    a,b,c,d=A;e,f,g,h=B
    return ((a*e+b*g)%3,(a*f+b*h)%3,(c*e+d*g)%3,(c*f+d*h)%3)
I=(1,0,0,1)
need(len(G)==48)
C3=[A for A in G if A!=I and mul(mul(A,A),A)==I]
need(len(C3)==8 and len({frozenset([I,A,mul(A,A)]) for A in C3})==4)
# Frob has trace 0, determinant 2, distinct eigenvalues +/-1 mod3.
need(S.Poly(x*x+2,x,modulus=3)==S.Poly((x-1)*(x+1),x,modulus=3))
print('BSD actual reduction points',pts,'plus O; 48 GL2, 4 cyclic Sylow-3 subgroups')

# NS: actual signed-cube polar Fourier triad, exact integer coefficients.
G=list(product(list(permutations(range(3))),list(product((-1,1),repeat=3))))
e=((0,1,2),(1,1,1))
def act(g,x):
    p,s=g; return tuple(s[i]*x[p[i]] for i in range(3))
def add(x,y):return tuple(a+b for a,b in zip(x,y))
def neg(x):return tuple(-a for a in x)
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def cross(x,y):return (x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
# use fixed deterministic centres and polarizations, found by search with exact checks
P=[(1,2,4),(2,-4,5),(-3,2,-9)]
V=[cross(p,v) for p,v in zip(P,[(1,0,0),(0,1,0),(0,0,1)])]
orb=[{act(g,p):act(g,v) for g in G} for p,v in zip(P,V)]
need(sum(map(len,orb))==144 and len(set.union(*(set(o) for o in orb)))==144)
need(all(dot(p,v)==0 for o in orb for p,v in o.items()))
need(all(o[neg(p)]==neg(v) for o in orb for p,v in o.items()))
# Fourier u=i v, omega=-p cross v, S=-sym(p tensor v)
def symterm(p,v,w,z):return -Q(dot(w,p)*dot(v,z)+dot(w,v)*dot(p,z),2)
# all distinct-label resonances and all six placements, coefficients of t1*t2*t3
hits=[]; coeff=Q(0)
for p,q in product(orb[0],orb[1]):
    r=neg(add(p,q))
    if r not in orb[2]:continue
    ps=[p,q,r];vs=[orb[i][k] for i,k in enumerate(ps)]
    w=[neg(cross(k,v)) for k,v in zip(ps,vs)]
    c=sum(symterm(ps[i],vs[i],w[j],w[k]) for i,j,k in permutations(range(3)))
    hits.append((ps,c));coeff+=c
need(len(hits)==48 and len({c for _,c in hits})==1 and coeff!=0)
print('NS 144 centres; 48 common-action triads; mixed signed enstrophy coefficient',coeff)

# Hodge: exact sign-character determinant transport on relative six slots.
# Diagonal sign reflections on the known relative generators; volume is sign.
for s in product((-1,1),repeat=6):
    R=S.diag(*s); need(R.T*R==S.eye(6)); need(R.det()==S.prod(s))
print('Hodge 64 determinant sign-character controls (abstract fixture)')
