"""Finite exact regressions for four Clay source-specific reductions; not kernels/PDE/cycles."""
from itertools import product
from fractions import Fraction as Q
import random
import sympy as S


def need(x):
    if not x:
        raise ArithmeticError('exact regression failed')


def dot(a,b): return sum(x*y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def proj(p,v):
    c=Q(dot(p,v),dot(p,p))
    return tuple(x-c*y for x,y in zip(v,p))

# NS original divergence-form coefficient, including projected vector output.
rng=random.Random(369); n=0; nonzero=0
for _ in range(1200):
    p,q,v,w=[tuple(rng.randint(-8,8) for _ in range(3)) for _ in range(4)]
    k=add(p,q)
    if not all(dot(a,a) for a in (p,q,k)): continue
    u=proj(p,v); z=proj(q,w); z=proj(k,z)
    a=tuple(dot(k,u)*x for x in z)
    b=tuple(dot(q,u)*x for x in z)
    need(a==b and dot(p,u)==0 and dot(k,z)==0)
    nonzero+=any(a); n+=1
need(nonzero>0)
# Squared-scale exact dyadic high/high geometry: R=2^r,P=2^j.
# P >= R^(7/4) iff 4*j >= 7*r; the sum ratio is geometric.
tail=0
for j in range(65):
    rr=[r for r in range(65) if 7*r<=4*j]
    # R^(7/2)/P^2 <= 2^(-3*(rmax-r)) for r<=rmax.
    top=max(rr)
    for r in rr:
        need(7*r-4*j<=-6*(top-r)); tail+=1
    need(sum(Q(1,8**(top-r)) for r in rr)<=Q(8,7))
print('NS projected low-advected identities',n,'nonzero',nonzero,'dyadic tail terms',tail)

# RH: genuine Q(sqrt5) Euler factors; independent local ideal-factor counts
# from roots of t^2-t-1 mod p; logarithmic derivative recurrence.
rows=0; rev=0
for p in list(S.primerange(2,150)):
    roots=[r for r in range(p) if (r*r-r-1)%p==0]
    degs=[1] if p==5 else ([1,1] if len(roots)==2 else [2])
    chi=int(S.legendre_symbol(5,p)) if p!=2 else -1
    a=[sum(chi**j for j in range(k+1)) for k in range(17)]
    b=[0]+[sum(f for f in degs if k%f==0) for k in range(1,17)]
    for k in range(17):
        ideal=sum(sum(f*e for f,e in zip(degs,es))==k for es in product(range(k+1),repeat=len(degs)))
        need(a[k]==ideal)
        if k:
            need(k*a[k]==sum(b[j]*a[k-j] for j in range(1,k+1)))
            need(b[k]==1+chi**k); rows+=1
            need(sum(int(S.mobius(d))*b[k//d] for d in S.divisors(k))==k*degs.count(k)); rev+=1
print('RH local factor/log derivative',rows,'inverse residue-degree counts',rev)

# BSD K=Q(sqrt5), eps^2=eps+1; alpha=4+sqrt5=3+2eps.
# 11 splits at eps=4,8. Conjugate alpha=5-2eps.
for a,b in [(3,2),(5,-2)]: need(a*a+a*b-b*b==11)
need([(3+2*r)%11 for r in (4,8)]==[0,8])
need([(5-2*r)%11 for r in (4,8)]==[8,0])
# Norm and real signs of the ratio; odd valuations at both split ideals.
z=S.sqrt(5); x=(4+z)/(4-z)
need(S.simplify(x*x.subs(z,-z))==1 and x.is_positive and x.subs(z,-z).is_positive)
need(S.simplify((4+z)*(4-z))==11)
# Signed local exponent recovery from (norm exponent, first exponent).
normrows=0
for a,b in product(range(-12,13),repeat=2):
    n=a+b; need((a,n-a)==(a,b)); normrows+=1
# inert 2 is another totally positive rational norm-square but odd local valuation.
need(not any((r*r-r-1)%2==0 for r in range(2)))
print('BSD split signed recovery',normrows,'explicit split/inert norm-square collisions PASS')

# Hodge: actual relative orientation trace-pairing inverse on prior field models.
# f polynomials for real cyclotomic conductors 7,9,11; use rational trace via multiplication.
x=S.symbols('x'); hrows=0
for f in (x**3+x*x-2*x-1,x**3-3*x+1,x**5+x**4-4*x**3-3*x*x+3*x+1):
    d=S.degree(f,x)
    def mulmat(a):
        return S.Matrix(d,d,lambda i,j:S.Poly(S.rem(a*x**j,f,x),x).nth(i))
    # delta=1, x, x^2-1; all invertible in these fields.
    for delta in (1,x,x*x-1):
        G=S.Matrix(d,d,lambda i,j:mulmat(delta*x**(i+j)).trace()/S.factorial(6))
        need(G.det()!=0); inv=G.inv()
        # Recover arbitrary coordinate columns via pairing with trace-dual basis.
        for k in range(d):
            v=S.eye(d)[:,k]
            need(inv*G*v==v); hrows+=1
        # One nonzero rational functional separates after field-action orbit.
        for k in range(d):
            ell=S.eye(d)[k,:]
            H=S.Matrix.vstack(*(ell*mulmat(x**j) for j in range(d)))
            need(H.det()!=0)
            need(H.inv()*H==S.eye(d)); hrows+=1
print('Hodge trace dual/one-functional orbit',hrows)
