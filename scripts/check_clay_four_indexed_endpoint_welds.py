#!/usr/bin/env python3
from collections import Counter
from itertools import product, permutations
from math import comb
import sympy as S

counts = Counter()
def ck(group, value):
    if not value:
        raise RuntimeError(group)
    counts[group] += 1

# RH: literal trapezoid residual cancels both first and second orders.
x,b=S.symbols('x b')
for n in range(3,12):
    f=sum(S.prod(b-j for j in range(k))*x**k/S.factorial(k) for k in range(n+1))
    g=sum(S.prod(b-1-j for j in range(k))*x**k/S.factorial(k) for k in range(n))
    r=S.Poly(S.expand(f-1-b*x*(1+g)/2),x)
    ck('RH',r.nth(0)==0)
    ck('RH',r.nth(1)==0)
    ck('RH',r.nth(2)==0)
    for k in range(3,n+1):
        ck('RH',S.factor(r.nth(k)-S.Rational(2-k,2)*S.prod(b-j for j in range(k))/S.factorial(k))==0)
for N in range(1,15):
    for s in range(-4,5):
        terms=[S.Rational(n)**(-s) for n in range(1,N+1)]
        lhs=(s-1)*(sum(terms)-terms[-1]/2)+S.Rational(N)**(1-s)
        rhs=S.Rational(s+1,2)+sum((s-1)*(terms[n-1]+terms[n])/2+S.Rational(n+1)**(1-s)-S.Rational(n)**(1-s) for n in range(1,N))
        ck('RH',lhs==rhs)
        if s in (0,1): ck('RH',lhs==S.Rational(s+1,2))

# BSD: quotient gauge, refinement and augmentation reconstruction.
def project(u,h):
    return [sum(u[i::h]) for i in range(h)]
def delta4(u):
    return [sum((-1)**(4-j)*comb(4,j)*u[(i-j)%len(u)] for j in range(5)) for i in range(len(u))]
def gauge(u):
    return [x-u[0] for x in u]
for p in (5,7,11):
    for m in (1,2):
        h=p**m
        for seed in range(1,7):
            u=[((i*i+3*seed*i+seed**2)%19)-9 for i in range(p*h)]
            um=project(u,h); w=gauge(u); wm=gauge(um)
            ck('BSD',project(delta4(u),h)==delta4(um))
            ck('BSD',delta4(wm)==delta4(um))
            ck('BSD',all(x-y==sum(w[::h]) for x,y in zip(project(w,h),wm)))
            ck('BSD',(sum(w)-sum(wm))%h==0)
            aug=sum(u)
            ck('BSD',(aug-sum(wm))%h==0)
            ck('BSD',[x+(aug-sum(wm))//h for x in wm]==um)
            ck('BSD',sum(w)% (p*h)==aug%(p*h))
            for j in range(h):
                ck('BSD',project(w,h)[j]-project(w,h)[0]==wm[j])

# NS: real periodic Galerkin triad, exact nonlinear energy cancellation
# and spectral variance/Rayleigh quotient identity, with physical phases.
p=(1,0,0); q=(0,2,0); r=(1,2,0)
neg=lambda k:tuple(-x for x in k)
K=[p,q,r,neg(p),neg(q),neg(r)]
vec={k:S.Matrix(k) for k in K}
P={k:S.eye(3)-vec[k]*vec[k].T/vec[k].dot(vec[k]) for k in K}
lam={k:vec[k].dot(vec[k]) for k in K}
def inner(u,v):
    return S.simplify(sum((u[k].conjugate().dot(v[k])).as_real_imag()[0] for k in K))
for a,b,c,sgn in product((1,2,3),(1,2),(1,2),(-1,1)):
    u={p:S.Matrix([0,0,a]),q:S.Matrix([b,0,0]),r:S.I*sgn*S.Matrix([0,0,c])}
    u.update({neg(k):v.conjugate() for k,v in list(u.items())})
    N={k:S.zeros(3,1) for k in K}
    for i,j in product(K,repeat=2):
        k=tuple(x+y for x,y in zip(i,j))
        if k in N: N[k]-=S.I*P[k]*(u[i].dot(vec[j])*u[j])
    Au={k:lam[k]*u[k] for k in K}
    E=inner(u,u); D=inner(u,Au); Z=inner(Au,Au); R=D/E
    V=Z-D**2/E; W=inner(Au,N); residual={k:Au[k]-R*u[k] for k in K}
    ck('NS',all(vec[k].dot(u[k])==0 and vec[k].dot(N[k])==0 for k in K))
    ck('NS',inner(u,N)==0)
    ck('NS',inner(u,residual)==0)
    ck('NS',inner(residual,residual)==V and V>0)
    ck('NS',inner(residual,N)==W)
    ck('NS',W!=0)
    for nu in (S.Rational(1,3),S.Rational(2,3),S.Integer(2)):
        dE=-2*nu*D; dD=2*W-2*nu*Z
        ck('NS',(dD*E-D*dE)/E**2==2*(W-nu*V)/E)
        ck('NS',2*(W-nu*V)/E<=inner(N,N)/(2*nu*E))

# Hodge: A3 x A3 commutes; invariant form dimension, and Kunneth
# vanishing when the three nontrivial effective line factors have H0=0.
perm=list(permutations(range(6)))
even=[p for p in perm if sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))%2==0]
for fixed in ((0,1,2),(0,1,3),(0,1,4),(0,1,5),(0,2,3),(0,2,4),(0,2,5),(0,3,4),(0,3,5),(0,4,5),(1,2,3),(1,2,4),(1,2,5),(1,3,4),(1,3,5),(1,4,5),(2,3,4),(2,3,5),(2,4,5),(3,4,5)):
    other=tuple(i for i in range(6) if i not in fixed)
    G=[g for g in even if all(g[i]==i for i in fixed)]
    H=[g for g in even if all(g[i]==i for i in other)]
    ck('Hodge',len(G)==len(H)==3)
    ck('Hodge',all(tuple(g[h[i]] for i in range(6))==tuple(h[g[i]] for i in range(6)) for g,h in product(G,H)))
    A=sum((S.eye(6)[:,list(g)] for g in G),S.zeros(6))/3
    ck('Hodge',A.rank()==4)
for degrees in product(range(3),repeat=3):
    if sum(degrees)==2: ck('Hodge',0 in degrees)
print(dict(counts),'TOTAL',sum(counts.values()))
