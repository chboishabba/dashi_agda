"""Exact source controls; not a kernel, PDE, Selmer, or Chow execution."""
from itertools import combinations, permutations, product
from fractions import Fraction as Q
import sympy as S


def need(b):
    if not b:
        raise ArithmeticError('regression failed')

# BSD: exact prime-level Sylow orders and selected good-reduction local data.
for ell in S.primerange(2, 100):
    order = (ell**2 - 1)*(ell**2 - ell)
    need(order % ell == 0 and order % ell**2 != 0)
# E: y^2+y=x^3, smooth at p != 3. Rational 3-torsion and local sizes.
counts = []
for p in S.primerange(2, 50):
    if p == 3:
        continue
    n = 1 + sum((y*y+y-x**3) % p == 0 for x,y in product(range(p), repeat=2))
    need(n % 3 == 0)
    counts.append((p, n))
print('BSD', len(list(S.primerange(2,100))), 'Sylow valuations;', len(counts), 'actual good-prime point counts', counts)

# NS: exact unnormalized signed Biot-Savart numerator and derivative identity.
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def cross(a,b): return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def neg(a): return tuple(-x for x in a)
def phi(x,y,r): return -dot(x,r)*dot(x,cross(y,r))
G = list(product(permutations(range(3)), product((-1,1), repeat=3)))
def det(g):
    p,s=g
    return S.prod(s)*(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
def polar(g,x):
    p,s=g
    return tuple(s[i]*x[p[i]] for i in range(3))
def axial(g,x): return tuple(det(g)*v for v in polar(g,x))
fixtures = [((1,2,3),(2,-3,1),(2,1,-1)), ((1,1,0),(0,1,1),(1,0,1)), ((1,0,0),(1,0,0),(0,1,2))]
for x,y,r in fixtures:
    for g in G:
        need(phi(axial(g,x),axial(g,y),polar(g,r)) == phi(x,y,r))
    need(phi(neg(x),neg(y),r) == -phi(x,y,r))
need(phi(*fixtures[0]) != 0)
# Multiply directional derivative of y cross r / |r|^3 by |r|^5.
r=S.Matrix(S.symbols('r0:3', real=True)); x=S.Matrix(S.symbols('x0:3', real=True)); y=S.Matrix(S.symbols('y0:3', real=True)); rr=r.dot(r)
numer = x.dot(y.cross(x)*rr - 3*y.cross(r)*r.dot(x))
need(S.expand(numer-3*phi(tuple(x),tuple(y),tuple(r))) == 0)
print('NS 144 actual axial/polar covariance checks, sign reversal and exact derivative')

# Hodge: actual split half-spin wedge-square Casimir interleaving.
# Basis e_i wedge e_j, i<j. Embed e_i wedge e_j as e_i tensor e_j-e_j tensor e_i.
def sign(seq): return (-1)**sum(seq[i]>seq[j] for i in range(len(seq)) for j in range(i+1,len(seq)))
basis = list(combinations(range(4),2))
def wedge(a,b):
    if a==b: return None,0
    return basis.index(tuple(sorted((a,b)))), 1 if a<b else -1
cas=[]
for I in basis:
    J=tuple(i for i in range(4) if i not in I)
    for x in (0,1):
        for y in (0,1):
            cas.append((I[x],I[1-x],J[y],J[1-y],sign(I+J)*(-1)**(x+y)))

def evaluate(shift):
    total=0; survivors=0
    for c in product(cas,repeat=3):
        a=[]; b=[]; w=1
        for i,j,k,l,s in c:
            a.extend((i,k)); b.extend((j,l)); w*=s
        idx=[]
        for i in range(6):
            q,s=wedge(a[i],b[(i+shift)%6]); idx.append(q); w*=s
        if w and len(set(idx))==6:
            total+=w*sign(idx); survivors+=1
    return total,survivors
values=[evaluate(j) for j in range(6)]
need(values[0][0]==0 and abs(values[1][0])==2880 and values[1][0]==-values[5][0])
print('Hodge 6 interleaving shifts, each 13824 terms:',values)
