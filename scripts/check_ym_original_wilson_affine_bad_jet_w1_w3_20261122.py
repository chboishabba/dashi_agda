#!/usr/bin/env python3
"""Exact two-Wilson *affine* marked bad-sector jet on original 4D words.

Proof/negative controls for the existing source-first affine KP W1/W3 boundary.
Uses a 512-state Q8 discrete conditional slice, NOT SU(2) Haar integration.
The universal affine inequalities in the companion source note apply to the
actual positive original compact-group Wilson Gibbs law.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
from sympy import Rational, symbols, diff, simplify, log, solve

L=4
origin=(0,0,0,0)
identity=(1,0,0,0)
Q8=[(sign,0,0,0) for sign in (1,-1)]
for axis in range(1,4):
    for sign in (1,-1):
        entry=[0,0,0,0];entry[axis]=sign;Q8.append(tuple(entry))
assert len(Q8)==8

def mult(p,q):
    a,b,c,d=p;e,f,g,h=q
    return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)

def inverse(q):return (q[0],-q[1],-q[2],-q[3])
def shift(x,axis):
    y=list(x);y[axis]=(y[axis]+1)%L;return tuple(y)
def plaquette(x,m,n):
    return ((x,m,1),(shift(x,m),n,1),(shift(x,n),m,-1),(x,n,-1))
def tr(word,config):
    h=identity
    for x,axis,sgn in word:
        z=config.get((x,axis),identity)
        h=mult(h,z if sgn==1 else inverse(z))
    assert h in Q8
    return h[0]

active=((origin,0),(shift(origin,0),0),(origin,1))
left=plaquette(origin,0,1)
right=plaquette(shift(origin,0),0,1)
plaquettes=[plaquette(x,m,n) for x in product(range(L),repeat=4)
            for m,n in combinations(range(4),2)]
affected=[w for w in plaquettes if any((x,a) in active for x,a,_ in w)]
assert len(plaquettes)==1536 and 0<len(affected)<=18

# Actual original Wilson 4D plaquette WORDS and source-dependent relative
# weights at beta=log(2), with 1021 links fixed and three Q8 links variable.
# Conditioning to Q8 is not the original Haar probability measure.
sectors=defaultdict(Q)
for elements in product(Q8,repeat=len(active)):
    config=dict(zip(active,elements))
    delta=sum(tr(w,config)-1 for w in affected)
    assert -2*len(affected)<=delta<=0
    f,g=tr(left,config),tr(right,config)
    bad=int(f<=0 and g<=0) # two neighbouring gauge-invariant bad plaquettes
    sectors[(f,g,bad)]+=Q(2)**delta
assert sum(sectors.values())>0

def data(s,t):
    full=[Q(0)]*8
    good=[Q(0)]*8
    for (f,g,b),w in sectors.items():
        h=w*(1+s*f)*(1+t*g)
        values=[h,h*f,h*g,h*f*g,
                w*f*(1+t*g),w*g*(1+s*f),w*f*g,Q(b)*h]
        into=good if not b else None
        full=[x+y for x,y in zip(full,values)]
        if into is not None:
            good=[x+y for x,y in zip(good,values)]
    z,zf,zg,zfg,zs,zt,zst,zb=full
    z0,gf,gg,gfg,gs,gt,gst,_=good
    assert z>z0>0 and 0<zb<z
    p=zb/z
    mean=lambda numer,denom:numer/denom
    covariance=mean(zfg,z)-mean(zf,z)*mean(zg,z)
    cov_good=mean(gfg,z0)-mean(gf,z0)*mean(gg,z0)
    db_s=zs-gs;db_t=zt-gt;db_st=zst-gst
    ps=db_s/z-zb*zs/z**2
    pt=db_t/z-zb*zt/z**2
    pst=(db_st/z-db_s*zt/z**2-db_t*zs/z**2
         -zb*zst/z**2+2*zb*zs*zt/z**3)
    # Cross derivative of log Z-full minus log Z-good.
    remainder=(zst/z-zs*zt/z**2)-(gst/z0-gs*gt/z0**2)
    via_p=pst/(1-p)+ps*pt/(1-p)**2
    assert remainder==via_p
    return p,ps,pt,pst,covariance,cov_good,remainder

p0=data(Q(0),Q(0))[0]
r=Q(9,100)
ratio=((1+r)/(1-r))**2
assert ratio==Q(11881,8281)
checks=0
for s,t in product((-r,-Q(1,25),Q(0),Q(1,25),r), repeat=2):
    p,ps,pt,pst,cov,covgood,remainder=data(s,t)
    assert p<=ratio*p0
    assert abs(ps)<=2*p/(1-r)
    assert abs(pt)<=2*p/(1-r)
    assert abs(pst)<=5*p/(1-r)**2
    assert abs(cov-covgood)<=6*p
    if s==0 and t==0: assert remainder==cov-covgood
    checks+=1

# Independently differentiate exact *source-first affine* bad ratio.
s,t=symbols('s t')
z=0;zb=0
for (f,g,b),w in sectors.items():
    h=Rational(w.numerator,w.denominator)*(1+s*f)*(1+t*g)
    z+=h;zb+=b*h
p=zb/z
for s0,t0 in ((0,0),(Rational(9,100),-Rational(1,25))):
    a=data(Q(s0),Q(t0))
    vals=(p,diff(p,s),diff(p,t),diff(p,s,t))
    exact=tuple(simplify(v.subs({s:s0,t:t0})) for v in vals)
    assert exact==a[:4]
    assert simplify(diff(log(z)-log(z-zb),s,t).subs({s:s0,t:t0}))==a[6]

# Mathematical source-identification negative control: a *global* F mark
# on joint occupancy of two compatible polymers cannot be reproduced by
# multiplying independent per-polymer affine marks whose one-polymer
# derivatives must vanish. Similarly normalized SU2 trace is nonmultiplicative.
a,b,u,v=symbols('a b u v')
true_z=(1+a)*(1+b)+s*a*b
naive=(1+a*(1+s*u))*(1+b*(1+s*v))
assert simplify(diff(true_z,s).subs(s,0))==a*b
assert simplify(diff(naive,s).subs(s,0)-(a*u+b*v+a*b*(u+v)))==0
assert solve((u,v,u+v-1),(u,v), dict=True)==[]
assert simplify(diff(naive,s).subs({s:0,u:0,v:0}))==0
qi=(0,1,0,0)
assert mult(qi,qi)==(-1,0,0,0)
assert mult(qi,qi)[0]==-1 and qi[0]*qi[0]==0
print('PASS 512 Q8 conditional original-plaquette-word configurations; affected plaquettes',len(affected))
print('PASS',checks,'rational two-source affine settings |s|,|t|<=9/100')
print('PASS source-tilt p<=11881/8281 p0, scores and mixed probability derivatives')
print('PASS exact logZ_full/logZ_good mixed jet and 6p covariance remainder at origin')
print('PASS independent SymPy affine ratio and mixed log differentiation')
print('PASS two-polymer global-mark and nonabelian trace factorization negative controls')
print('SOURCE SCOPE: Q8 discrete slice != full SU2 Haar; no KP Wilson activity, CMP116, W3 physical estimate or Agda kernel')
