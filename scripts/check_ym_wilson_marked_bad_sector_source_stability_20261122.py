#!/usr/bin/env python3
"""Original 4D Wilson-word Q8 finite slice: exact two-mark bad-sector stability.

The Q8 assignments form a discrete 3-active-link conditional slice,
NOT the original SU(2) Haar law. Universal inequalities used below apply
to the true normalized original Wilson Gibbs measure, by positivity and
absolute bounds on the marked real Wilson observables. They do NOT prove
KP cluster charges, CMP116 physical localization, or a mass gap.
"""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from sympy import Rational, symbols, diff, simplify

L=4
O=(0,0,0,0)
ONE=(1,0,0,0)
Q8=[(s,0,0,0) for s in (1,-1)]
for j in range(1,4):
    for sg in (1,-1):
        q=[0,0,0,0];q[j]=sg;Q8.append(tuple(q))

def mul(p,q):
    a,b,c,d=p;e,f,g,h=q
    return (a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e)
def inv(q): return (q[0],-q[1],-q[2],-q[3])
def shift(x,k):
    y=list(x);y[k]=(y[k]+1)%L;return tuple(y)
def plaquette(x,mu,nu):
    return ((x,mu,1),(shift(x,mu),nu,1),
            (shift(x,nu),mu,-1),(x,nu,-1))
ACTIVE=((O,0),(shift(O,0),0),(O,1))
LEFT=plaquette(O,0,1)
RIGHT=plaquette(shift(O,0),0,1)
allp=[plaquette(x,mu,nu) for x in product(range(L),repeat=4)
      for mu,nu in combinations(range(4),2)]
affected=[p for p in allp if any((x,mu) in ACTIVE for x,mu,_ in p)]
assert len(Q8)==8 and len(allp)==1536 and len(affected)<=18
def tr(w,config):
    q=ONE
    for x,mu,sgn in w:
        v=config.get((x,mu),ONE)
        q=mul(q,v if sgn==1 else inv(v))
    assert q in Q8
    return q[0]

# Positive conditional discrete Wilson weight at beta=log(2), with
# all non-active original links fixed to I. Global constant cancels.
sectors=defaultdict(Fraction)
for qs in product(Q8,repeat=3):
    config=dict(zip(ACTIVE,qs))
    delta=sum(tr(p,config)-1 for p in affected)
    assert -2*len(affected)<=delta<=0
    f,g=tr(LEFT,config),tr(RIGHT,config)
    bad=int(f<=0 and g<=0)
    sectors[(f,g,bad)]+=Fraction(2)**delta

def moments(x,y):
    A=defaultdict(Fraction)
    for (f,g,b),w in sectors.items():
        v=w*Fraction(x)**f*Fraction(y)**g
        for key,t in (("Z",1),("F",f),("G",g),("FG",f*g),
                      ("B",b),("BF",b*f),("BG",b*g),
                      ("BFG",b*f*g),("GF",(1-b)*f),
                      ("GG",(1-b)*g),("GFG",(1-b)*f*g)):
            A[key]+=v*t
    z=A["Z"]
    E=lambda k:A[k]/z
    p=E("B"); ef=E("F"); eg=E("G")
    cov=E("FG")-ef*eg
    ds=E("BF")-p*ef
    dst=E("BFG")-E("BF")*eg-E("BG")*ef+p*ef*eg-p*cov
    zg=z-A["B"]
    assert zg>0
    cov_good=A["GFG"]/zg-A["GF"]*A["GG"]/zg**2
    assert abs(cov-cov_good)<=6*p
    return p,ds,dst,cov
p0=moments(1,1)[0]
assert 0<p0<1
for x,y in ((1,1),(2,1),(1,3),(2,3),(3,2),(4,4)):
    p,ds,dst,cov=moments(x,y)
    assert p<=Fraction(x*y)**2*p0
    assert abs(ds)<=2*p
    assert abs(dst)<=5*p
    assert abs(cov)<=1

# Confirm the source-mark derivatives from an independent SymPy expression.
x,y=symbols("x y",positive=True)
z=0;zb=0
for (f,g,b),w in sectors.items():
    term=Rational(w.numerator,w.denominator)*x**f*y**g
    z+=term;zb+=b*term
prob=zb/z
Ds=lambda v:simplify(x*diff(v,x))
Dt=lambda v:simplify(y*diff(v,y))
for x0,y0 in ((1,1),(2,3)):
    exact=tuple(simplify(v.subs({x:x0,y:y0}))
                for v in (prob,Ds(prob),Dt(Ds(prob))))
    assert exact==moments(x0,y0)[:3]
print("PASS: 512/512 original 4D Wilson plaquette-word Q8 conditional slice")
print("PASS: exact SymPy real two-source bad-sector mixed derivative identity")
print("PASS: P_st(B)<=exp(2(|s|+|t|))P_0(B), |Ds|<=2P_st(B), |Dst|<=5P_st(B)")
print("PASS: full vs good-conditioned covariance difference <= 6P_st(B)")
print("NOT CLAIMED: SU2 Haar integration, polymer cluster activity, W3, continuum, Agda")
