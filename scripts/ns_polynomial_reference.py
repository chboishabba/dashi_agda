#!/usr/bin/env python3
"""Exact rational Fourier-path validator for periodic unforced NS.
Classical critical Fourier norm: Lei--Lin, DOI:10.1002/cpa.20361; arXiv:1203.2699.
DASHI: piecewise polynomial residual and same-data refinement certificate.
No universal regularity claim. See controlling four-P0 roadmap.
"""
from fractions import Fraction as Q
from math import isqrt

ZERO=(0,)*6
SCALE=10**10

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(c,a): return tuple(c*x for x in a)
def neg(k): return tuple(-x for x in k)
def lam(k): return sum(x*x for x in k)
def conj(a): return a[:3]+scale(-1,a[3:])
def dot(k,a): return sum(x*y for x,y in zip(k,a))
def proj(k,a):
    return tuple(x-Q(dot(k,a[:3]),lam(k))*j for x,j in zip(a[:3],k))+tuple(x-Q(dot(k,a[3:]),lam(k))*j for x,j in zip(a[3:],k))
def put(u,k,a):
    v=add(u.get(k,ZERO),a)
    if any(v): u[k]=v
    else: u.pop(k,None)
def lin(*terms):
    out={}
    for c,u in terms:
        for k,a in u.items(): put(out,k,scale(c,a))
    return out
def bilinear(u,v):
    out={}
    for k,a in u.items():
        for l,b in v.items():
            m=add(k,l)
            if not any(m): continue
            x,y=dot(l,a[:3]),dot(l,a[3:])
            if x or y:
                # i (a dot l) b, retaining both phases
                w=tuple(-x*t-y*s for s,t in zip(b[:3],b[3:]))+tuple(x*s-y*t for s,t in zip(b[:3],b[3:]))
                put(out,m,w)
    return {k:w for k,a in out.items() if any(w:=proj(k,a))}
def lap(u): return {k:scale(lam(k),a) for k,a in u.items()}
def cut(u,K): return {k:a for k,a in u.items() if lam(k)<=K*K}
def cos_mode(k,a,amp):
    w=scale(Q(amp,2),tuple(a)+(0,)*3)
    return {k:w,neg(k):w} if amp else {}
def fixture():
    return lin((1,cos_mode((0,1,0),(1,0,0),Q(1))), (1,cos_mode((1,0,0),(0,0,1),Q(1,8))), (1,cos_mode((1,0,1),(0,1,0),Q(1,8))))
def check(u):
    for k,a in u.items():
        if len(k)!=3 or not all(type(x) is int for x in k) or not any(k) or len(a)!=6 or not all(type(x) in (int,Q) for x in a): raise ValueError('invalid exact nonzero Fourier coordinate')
        if dot(k,a[:3]) or dot(k,a[3:]) or u.get(neg(k),ZERO)!=conj(a): raise ValueError('non-solenoidal or non-real reference')
def up(x):
    x=Q(x)*SCALE
    return Q(-(-x.numerator//x.denominator),SCALE)
def sqrt_bounds(x):
    x=Q(x)*SCALE*SCALE
    a=isqrt(x.numerator//x.denominator)
    return Q(a,SCALE),Q(a+(a*a*x.denominator!=x.numerator),SCALE)
def norm(u,critical=False):
    return sum((sqrt_bounds(sum(x*x for x in a))[1]/(sqrt_bounds(lam(k))[0] if critical else 1) for k,a in u.items()),Q(0))
def eval_end(poly): return lin(*((1,u) for u in poly))
def rounded(u):
    return {k:w for k,a in u.items() if any(w:=proj(k,tuple(Q(round(Q(x)*SCALE),SCALE) for x in a)))}
def build(initial,K,dt,steps,degree=2,nu=Q(1)):
    if type(K) is not int or K<1 or type(steps) is not int or steps<0 or type(degree) is not int or degree<1 or type(dt) not in (Q,int) or dt<=0 or type(nu) not in (Q,int) or nu<=0: raise ValueError('invalid builder controls')
    check(initial)
    state=cut(initial,K); path=[]
    for _ in range(steps):
        poly=[state]
        for j in range(degree):
            rhs=lin((-nu,lap(poly[j])),*((-1,bilinear(poly[i],poly[j-i])) for i in range(j+1)))
            poly.append(cut(lin((Q(dt,j+1),rhs)),K))
        path.append((dt,poly)); state=rounded(eval_end(poly))
    return path

def residual(dt,poly,nu):
    # Full, not truncated: signed r=v_t+nu A v+B(v,v).
    d=len(poly)-1; result=[]
    for j in range(2*d+1):
        terms=[(1,bilinear(poly[i],poly[j-i])) for i in range(max(0,j-d),min(j,d)+1)]
        if j<=d: terms.append((nu,lap(poly[j])))
        if j<d: terms.append((Q(j+1,dt),poly[j+1]))
        result.append(lin(*terms))
    return result

def exp_upper(x):
    # exp(x)<= (1-x/n)^(-n) for 0<=x<n.
    n=max(16,2*(-(-x.numerator//x.denominator)+1))
    return up((1-x/n)**(-n))

def validate(path,initial,nu):
    if type(nu) not in (Q,int) or nu<=0: raise ValueError('positive exact viscosity required')
    check(initial); last=initial; error=Q(0); peak=Q(0)
    for dt,poly in path:
        if type(dt) not in (Q,int) or dt<=0 or not poly: raise ValueError('invalid interval')
        for u in poly: check(u)
        jump=norm(lin((1,last),(-1,poly[0])),True)
        v0=sum((norm(u) for u in poly),Q(0))
        c=dt*sum((norm(u,True)/ (j+1) for j,u in enumerate(residual(dt,poly,nu))),Q(0))
        error=up(exp_upper(Q(2,nu)*dt*v0*v0)*(error+jump+c))
        if error>=nu/2: raise ValueError('strict error budget exceeded')
        peak=max(peak,error); last=eval_end(poly)
    return peak,up(norm(last,True)+error)

if __name__=='__main__':
    u=fixture(); path=build(u,2,Q(1,32),4)
    e,t=validate(path,u,Q(1))
    print('initial critical upper',norm(u,True),'peak error',e,'terminal critical upper',t)
