#!/usr/bin/env python3
"""Original SU(N) Wilson high-beta local-energy-excess shell: exact audit.
Weyl measure and continuous compact-group conditional bounds are proved in
Docs/physics/YMClayOriginalSUNHighBetaWeylCapEnergyExcessShell20261123.md.
Local arithmetic/geometry checks only, NOT full Haar quadrature or OS gap.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import factorial
from random import Random
import mpmath as mp
mp.mp.dps = 45
checks = 0

def ok(p):
    global checks
    assert p
    checks += 1

def K(N):
    return factorial(N)*(128*N*N)**(N-1)*(16*N)**(N*(N-1))

def torus_box(N,delta,values):
    h=delta/(4*N)
    eps=delta/(32*N*N)
    centres=[F(2*j-N-1,2)*h for j in range(1,N+1)]
    angles=[centres[j]+eps*values[j] for j in range(N-1)]
    angles.append(-sum(angles))
    return angles

rng=Random(20261123)
for N in range(2,9):
    for delta in [F(1,4),F(1,8),F(1,16)]:
        for _ in range(30):
            t=torus_box(N,delta,[F(rng.randint(-100,100),100) for _ in range(N-1)])
            ok(sum(t)==0 and all(abs(x)<delta for x in t))
            ok(min(abs(t[i]-t[j]) for i,j in combinations(range(N),2)) >= delta/(8*N))
            differences=[mp.mpf((t[i]-t[j]).numerator)/(t[i]-t[j]).denominator
                         for i,j in combinations(range(N),2)]
            vand=mp.fprod(2-2*mp.cos(x) for x in differences)
            lower=(mp.mpf(delta.numerator)/(delta.denominator*16*N))**(N*(N-1))
            ok(vand >= lower)

for N in range(2,7):
    from itertools import permutations
    perms=list(permutations(range(N)))
    ct=sum(int(__import__('sympy').LeviCivita(*p)*__import__('sympy').LeviCivita(*q))
           for p in perms for q in perms
           if all(p[j]-q[j]==p[-1]-q[-1] for j in range(N-1)))
    ok(ct==factorial(N))

# Reuse EXACT source original 8/12-color classes, not a new colourer.
def color(L,x,mu):
    k=2 if L%2==0 else 3
    def c(j): return (j%2 if L%2==0 or j<L-1 else 2)
    return (mu,sum(c(x[j]) for j in range(4) if j!=mu)%k)

def step(L,x,mu):
    y=list(x);y[mu]=(y[mu]+1)%L;return tuple(y)

for L in range(3,8):
    for x in product(range(L),repeat=4):
        for mu,nu in combinations(range(4),2):
            links=[(x,mu),(step(L,x,mu),nu),(step(L,x,nu),mu),(x,nu)]
            ok(len({color(L,y,d) for y,d in links})==4)

for N in range(2,7):
    for kappa in (8,12):
        beta=mp.mpf(16)
        logp=lambda b: mp.log(K(N))+(N*N-1)*mp.log(b)+6-b
        while logp(beta)/kappa+mp.log(196)>=0:
            beta*=2
        p=mp.exp(logp(beta))
        q=196*p**(mp.mpf(1)/kappa)
        ok(0<q<1)
        for n in range(1,81):
            ok(p**((n+kappa-1)//kappa) <= p**(mp.mpf(n)/kappa))
        for m in (1,4,19):
            ok(p**(mp.mpf(1)/kappa)*q**(m-1)/(1-q)>0)

# ORIGINAL L4 continuous SU2 negative-control staple geometry.
# Opposite transverse links are 3(-I), 3(+I), so the 6-staple sum
# vanishes as a 2x2 matrix and the local energy equals 6 for ALL U.
L=4;x=(0,0,0,0);mu=0
ext={}
for nu in (1,2,3):
    ext[(step(L,x,nu),mu)]=-1
    y=list(x);y[nu]=(y[nu]-1)%L
    ext[(tuple(y),mu)]=1

def value(edge,s):return s if edge==(x,mu) else ext.get(edge,1)
def plaquette(y,nu,s):
    return value((y,mu),s)*value((step(L,y,mu),nu),s)*value((step(L,y,nu),mu),s)*value((y,nu),s)
for s in (-1,1):
    traces=[]
    for nu in (1,2,3):
        y=list(x);y[nu]=(y[nu]-1)%L
        traces.extend((plaquette(x,nu,s),plaquette(tuple(y),nu,s)))
    ok(sorted(traces)==[-1,-1,-1,1,1,1])
    ok(sum(1-t for t in traces)==6)
print(f'PASS {checks} independent exact geometry, Weyl-denominator and threshold checks')
print('SU(N) original high-beta local-excess animal rate is conditional on the selected event.')
print('Counterexample: 3 frustrated incident plaquettes, local excess = 0.')
print('No original CMP119/122 W3 physical cluster or same-H mass gap claimed.')
