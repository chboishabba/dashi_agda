#!/usr/bin/env python3
from collections import Counter
from itertools import product
from fractions import Fraction as F
from math import comb
import sympy as S

counts = Counter()
def ck(group, value):
    if not value:
        raise RuntimeError(group)
    counts[group] += 1

# RH: rational two-sided Cayley log bounds, with quadratic/cubic residuals.
for n in range(1,65):
    x=F(1,n); y=x/(2+x)
    for j in range(1,7):
        lo=2*sum(y**(2*k+1)/ (2*k+1) for k in range(j))
        hi=lo+2*y**(2*j+1)/((2*j+1)*(1-y*y))
        ck('RH',0<lo<=hi<=x)
        ck('RH',lo>=x-x*x/2)
        ck('RH',hi<=x-x*x/2+x**3/3)
        ck('RH',hi-lo==2*y**(2*j+1)/((2*j+1)*(1-y*y)))

# BSD: constructive repeated cyclic antidifference, with integral gauge.
def diff(u):
    return [u[i-1]-u[i] for i in range(len(u))]
def aug(u):
    return sum(u)
def antidiff(d, target_aug):
    if aug(d): raise ValueError('nonzero source augmentation')
    w=[0]
    for i in range(1,len(d)): w.append(w[-1]-d[i])
    a=target_aug-aug(w)
    if a%len(d): raise ValueError('incompatible augmentation')
    return [v+a//len(d) for v in w]
for p,m,seed in product((5,7,11),(1,2),range(1,6)):
    h=p**m; u=[(i*i+seed*i+seed**2)%23-11 for i in range(h)]
    tower=[u]
    for _ in range(4): tower.append(diff(tower[-1]))
    d=tower[-1]
    for j in range(3,-1,-1):
        d=antidiff(d, aug(tower[j]))
        ck('BSD',d==tower[j])
    for r in range(1,4): ck('BSD',sum(comb(i,r)*tower[-1][i] for i in range(h))%h==0)
    try: antidiff(tower[-1],1)
    except ValueError: ck('BSD',True)
    else: ck('BSD',False)

# NS: literal divergence-free Fourier velocity, with nested cutoffs and
# exact physical difference equation. A 2D3C shear/passive scalar sector.
def add(k,l): return tuple(a+b for a,b in zip(k,l))
def neg(k): return tuple(-x for x in k)
def lam(k): return sum(x*x for x in k)
def proj(k):
    v=S.Matrix(k)
    return S.eye(3)-v*v.T/lam(k)
def get(u,k): return u.get(k,S.zeros(3,1))
def cut(u,R): return {k:v for k,v in u.items() if 0<lam(k)<=R*R}
def bil(u,v,R):
    out={}
    for k,a in u.items():
        for l,b in v.items():
            j=add(k,l)
            if 0<lam(j)<=R*R:
                out[j]=get(out,j)+S.I*proj(j)*(a.dot(S.Matrix(l))*b)
    return out
def lin(*terms):
    keys=set().union(*(d for _,d in terms))
    return {k:sum((c*get(d,k) for c,d in terms),S.zeros(3,1)) for k in keys}
def same(u,v): return all(get(u,k)==get(v,k) for k in set(u)|set(v))
def norm(u): return sum(S.expand(v.conjugate().dot(v)) for v in u.values())
def inner(u,v):
    return S.re(sum(get(u,k).conjugate().dot(get(v,k)) for k in set(u)|set(v)))
for a,b,c in product((1,2),(1,3),(1,2)):
    src={(0,1,0):S.Matrix([S.I*a,0,0]),(1,0,0):S.Matrix([0,0,b]),(1,1,0):S.Matrix([0,0,S.I*c]),(2,1,0):S.Matrix([0,0,a+b])}
    src.update({neg(k):v.conjugate() for k,v in list(src.items())})
    for K,M in ((1,2),(1,4),(2,3),(2,5)):
        v=cut(src,K); u=cut(src,M); e=lin((1,u),(-1,v))
        bv=bil(v,v,M); r=lin((-1,bv),(1,cut(bv,K)))
        lhs=lin((-1,bil(u,u,M)),(1,bil(v,v,K)))
        rhs=lin((-1,bil(v,e,M)),(-1,bil(e,v,M)),(-1,bil(e,e,M)),(1,r))
        ck('NS',same(lhs,rhs))
        ck('NS',all(lam(k)>K*K or get(r,k)==S.zeros(3,1) for k in r))
        ck('NS',all(lam(k)<=4*K*K or get(r,k)==S.zeros(3,1) for k in r))
        ck('NS',inner(u,bil(u,u,M))==0)
        ck('NS',all(get(bil(u,u,M),k)[0]==0 and get(bil(u,u,M),k)[1]==0 for k in bil(u,u,M)))
        D=sum(lam(k)*norm({k:w}) for k,w in u.items())
        Umax=sum(abs(w[0]) for w in u.values())
        ck('NS',norm(bil(u,u,M))<=Umax**2*D)
# Exact Young remainder at its maximizing scale and arbitrary square roots.
for nu,C,X,y in product(map(S.Rational,(1,2,3)),map(S.Rational,(1,2)),map(S.Rational,(1,2)),map(S.Rational,range(1,9))):
    # Y=y^4, X here is the fourth root of enstrophy.
    ck('NS',C*X**3*y**3-nu*y**4/4<=S.Rational(27,4)*C**4*X**12/nu**3)
print(dict(counts),'TOTAL',sum(counts.values()))
