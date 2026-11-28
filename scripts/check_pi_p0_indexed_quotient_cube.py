#!/usr/bin/env python3
"""Paper 9 indexed source/root/gauge cube; exact integer oracle, UNEXECUTED.
Not a production evaluator, timing result, or proof of the analytic pi identity.
Reuses the original scheduler leaf formula and independently computes its gcd.
"""
from dataclasses import dataclass
from itertools import permutations, combinations
from math import gcd, isqrt, prod

A, B, C = 13591409, 545140134, 640320**3

def require(ok, label):
    if not ok:
        raise AssertionError(label)

def raw_leaf(j):
    if j == 0:
        return 1, 1, A
    p = -24*(2*j-1)*(6*j-5)*(6*j-1)
    q = C*j**3
    return p, q, p*(A+B*j)

def scale_leaf(j):
    p,q,_ = raw_leaf(j)
    return gcd(abs(p),q)

def source_scale(i,j):
    return prod(scale_leaf(t) for t in range(i,j))

def join(l,r):
    p,q,t = l
    u,v,w = r
    return p*u, q*v, t*v+p*w

def scaled(t,g):
    return tuple(g*x for x in t)

def split(i,j,raw):
    out=(1,1,0)
    for k in range(i,j):
        leaf=raw_leaf(k)
        if not raw:
            g=scale_leaf(k)
            require(all(x%g==0 for x in leaf),"leaf exact gauge")
            leaf=tuple(x//g for x in leaf)
        out=join(out,leaf)
    return out

@dataclass(frozen=True)
class State:
    n:int
    bits:int
    digits:int
    raw:bool
    p:int
    q:int
    t:int
    R:int
    x:int
    W:int

def direct(n,b,d,raw):
    p,q,t=split(0,n,raw)
    R=isqrt(10005 << (2*b))
    Z=426880*5**d*q
    D=1<<(b-d)
    x,W=divmod(Z*R,D*t)
    return State(n,b,d,raw,p,q,t,R,x,W)

def step(s,axis,m,bnew):
    n,b,d,raw,p,q,t,R,x,W=(
        s.n,s.bits,s.digits,s.raw,s.p,s.q,s.t,s.R,s.x,s.W)
    D=1<<(b-d)
    Z=426880*5**d*q
    if axis=="gauge":
        require(not raw,"gauge direction")
        g=source_scale(0,n)
        p,q,t=scaled((p,q,t),g)
        W*=g
        raw=True
    elif axis=="root":
        shift=bnew-b
        require(shift>=0,"root refinement direction")
        r=isqrt(10005<<(2*bnew))-(R<<shift)
        require(0<=r<1<<shift,"nested radical digit")
        R=(R<<shift)+r
        D <<= shift
        W=(W<<shift)+Z*r
        b=bnew
    elif axis=="source":
        require(m>=n,"suffix direction")
        ps,qs,ts=split(n,m,raw)
        # Same raw or normalized chart; original index is not relabelled.
        W=qs*W-D*x*p*ts
        p,q,t=join((p,q,t),(ps,qs,ts))
        n=m
    else:
        raise ValueError(axis)
    h,W=divmod(W,D*t)
    return State(n,b,d,raw,p,q,t,R,x+h,W)

def check_state(s):
    D=1<<(s.bits-s.digits)
    Z=426880*5**s.digits*s.q
    require(s==direct(s.n,s.bits,s.digits,s.raw),"direct independent prefix/root quotient")
    require(Z*s.R==D*s.x*s.t+s.W and 0<=s.W<D*s.t,"reopen original numerator")
    qn=C*s.n**3
    pn=-24*(2*s.n-1)*(6*s.n-5)*(6*s.n-1)
    delta=s.p*pn*(A+B*s.n)
    V=qn*s.t+delta
    require(V>0 and (delta>0)==(s.n%2==0),"original signed edge")
    rho,ell=divmod(s.W,D)
    if s.n%2==0:
        carry,eta=divmod(qn*ell,D)
        F=qn*rho-s.x*delta+carry
        h,r=divmod(F,V)
        x=s.x+h
        require(F<V and qn*Z*s.R==D*(x*V+r)+eta,"corrected quotient reopening")
        require(x==qn*Z*s.R//(D*V),"corrected direct floor")
    else:
        x=s.x
    # Literal upper admission and both retry predicates; independent of COMP6e.
    a,bb,Nh,Nl=(qn,1,V,s.t) if s.n%2==0 else (1,qn,s.t,V)
    Y=Z*s.R
    corners=(bb*(Y+Z)-D*(x+1)*Nl,bb*Y-D*(x+1)*Nl,
             a*(Y+Z)-D*(x+1)*Nh)
    return x,corners,delta

def main():
    cubes=faces=paths=states=gauge_checks=0
    axes=("source","root","gauge")
    for n in range(2,10):
      for m in (n,n+1,n+3):
       for d in (1,7,28):
        for b in (d,4*d+16):
         for bnew in (b,b+1,b+65):
          start=direct(n,b,d,False)
          vertices={}
          for size in range(4):
           for subset in combinations(axes,size):
            out=start
            for a in subset:
                out=step(out,a,m,bnew)
            vertices[frozenset(subset)]=out
            check_state(out)
            states+=1
          for a,baxis in combinations(axes,2):
            other=next(c for c in axes if c not in (a,baxis))
            for fixed in (frozenset(),frozenset((other,))):
                s=vertices[fixed]
                ab=step(step(s,a,m,bnew),baxis,m,bnew)
                ba=step(step(s,baxis,m,bnew),a,m,bnew)
                require(ab==ba==vertices[fixed|{a,baxis}],"cube face")
                faces+=1
          for order in permutations(axes):
            out=start
            for a in order:
                out=step(out,a,m,bnew)
            require(out==vertices[frozenset(axes)],"cube endpoint path")
            paths+=1
          for subset in (frozenset(),frozenset(("source",)),frozenset(("root",)),frozenset(("source","root"))):
            norm=vertices[subset]
            raw=vertices[subset|{"gauge"}]
            g=source_scale(0,norm.n)
            x,c,e=check_state(norm)
            xr,cr,er=check_state(raw)
            require(x==xr and cr==scaled(c,g) and er==g*e,"signed gauge transport")
            require(raw.W==g*norm.W,"full residual gauge")
            gauge_checks+=1
          cubes+=1
    print(f"cubes={cubes} faces={faces} paths={paths} states={states} gauge={gauge_checks} PASS")

if __name__=="__main__":
    main()
