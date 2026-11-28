#!/usr/bin/env python3
"""Exact rational Fourier-path validator for periodic unforced NS.
Classical critical Fourier norm: Lei--Lin, DOI:10.1002/cpa.20361; arXiv:1203.2699.
DASHI: piecewise polynomial residual and same-data refinement certificate.
No universal regularity claim. See controlling four-P0 roadmap.
"""
from fractions import Fraction as Q
from math import isqrt, comb

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

def bernstein(poly):
    """Convert power coefficients on [0,1] to Bernstein coefficients."""
    d=len(poly)-1
    if d<0: raise ValueError('empty polynomial')
    return [lin(*((Q(comb(i,j),comb(d,j)),poly[j]) for j in range(i+1))) for i in range(d+1)]

def growth(v,beta):
    # max(0, sup_{x>=1} (2*v*x-beta*x*x)), with positive beta.
    if v<0 or beta<=0: raise ValueError('invalid growth parameters')
    return max(Q(0), 2*v-beta if v<=beta else v*v/beta)

def cube_tail_upper(R,s,homogeneous_norm_squared):
    """Upper critical norm of modes |k|_infty>R from an H^s bound.

    Caller must supply a certified bound on the squared homogeneous norm
    of that tail (or entire datum). R and s are positive integers.
    """
    if type(R) is not int or R<1 or type(s) is not int or s<1 or type(homogeneous_norm_squared) not in (Q,int) or homogeneous_norm_squared<0:
        raise ValueError('invalid tail norm bound')
    return sqrt_bounds(Q(26)*homogeneous_norm_squared/((2*s-1)*R**(2*s-1)))[1]

def _validate_bernstein(path,initial,nu,budget,initial_tail,polarized):
    """Critical-norm bound with Bernstein enclosure and retained dissipation.

    Charge every seam. Reserve positive dissipation for H.
    The symmetric option uses q<2*nu and beta=nu-q/2-delta;
    the original estimate uses q<nu and beta=nu-q-delta.
    initial_tail is a caller-certified bound for the unrepresented datum.
    No assertion of existence when validation fails.
    """
    if type(nu) not in (Q,int) or nu<=0: raise ValueError('positive exact viscosity required')
    q=Q(nu,4 if polarized else 8) if budget is None else budget
    if type(q) not in (Q,int) or not 0<q<(2*nu if polarized else nu): raise ValueError('invalid strict budget')
    available=nu-(Q(q,2) if polarized else q)
    delta=min(Q(nu,8),Q(available,2)); beta=available-delta
    if type(initial_tail) not in (Q,int) or not 0<=initial_tail<q: raise ValueError('invalid initial tail bound')
    check(initial); last=initial; error=Q(initial_tail); peak=error
    for dt,poly in path:
        if type(dt) not in (Q,int) or dt<=0 or not poly: raise ValueError('invalid interval')
        for u in poly: check(u)
        jump=norm(lin((1,last),(-1,poly[0])),True)
        v0=max(norm(u) for u in bernstein(poly))
        rb=bernstein(residual(dt,poly,nu))
        c=dt*sum((norm(u,True) for u in rb),Q(0))/len(rb)
        error=up(exp_upper(dt*(polarized_growth(v0,beta) if polarized else growth(v0,beta)))*(error+jump+c))
        if error>=q: raise ValueError('strict error budget exceeded')
        peak=max(peak,error); last=eval_end(poly)
    return peak,up(norm(last,True)+error)

def polarized_growth(v,beta):
    """Symmetric projected interaction has mixed coefficient V0, not 2 V0."""
    return growth(Q(v,2),beta)

def validate_tight(path,initial,nu,budget=None,*,initial_tail=Q(0)):
    """Original Bernstein estimate; preserve its exact legacy bounds."""
    return _validate_bernstein(path,initial,nu,budget,initial_tail,False)

def validate_polarized(path,initial,nu,budget=None,*,initial_tail=Q(0)):
    """Use the paired Leray bound E' + (nu-E/2)H <= V0 G + c.

    Strict q<2 nu with positive reserved dissipation. Terminal critical
    bound <2 nu suffices for smooth global small-critical-norm continuation.
    This is not a universal regularity guarantee.
    """
    return _validate_bernstein(path,initial,nu,budget,initial_tail,True)

if __name__=='__main__':
    u=fixture(); path=build(u,2,Q(1,32),4)
    e,t=validate(path,u,Q(1))
    print('initial critical upper',norm(u,True),'peak error',e,'terminal critical upper',t)
