#!/usr/bin/env python3
"""BR52: eight-order SAME-SOURCE moving-material ADM conormal jets.

This is a substantial all-channel extension of BR48–51: keep 15 symmetric
metric and five subsidiary coordinate jets, all 5 spacetime derivatives,
moving F=n-f and source ADM N,H,v,D, including *all* time derivatives
of graph tilt, lapse, shift, inverse metric and volume density through order 8.

Exact truncated Taylor coefficients are the canonical divided jets.
The coefficient convolution implements ALL Leibniz terms automatically;
no spurious factorial products or missing q_t*j_t cross terms.

Physical ADM reference: H diagonal positive near t=0. The full nonlinear
and non-diagonal source must instantiate the same geometry in Agda; this
symbolic checker proves an exact source-family identity, not a tame PDE norm
or uniform all-background result.

--part all|metric|gauge|negative
"""
from fractions import Fraction as F
import argparse
from math import factorial

ORDER=8

def trim(a):
    v=list(a)[:ORDER+1]
    return tuple(v+[F(0)]*(ORDER+1-len(v)))
def const(v):return trim([F(v)])
def var(c0,c1=0,c2=0):
    return trim([F(c0),F(c1),F(c2)])
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    return tuple(sum((a[k]*b[n-k] for k in range(n+1)),F(0))
                  for n in range(ORDER+1))
def scale(c,a):return tuple(F(c)*x for x in a)
def reciprocal(a):
    if a[0]==0:raise ZeroDivisionError("source lapse/spatial inverse zero")
    b=[F(1)/a[0]]
    for n in range(1,ORDER+1):
        b.append(-sum((a[k]*b[n-k] for k in range(1,n+1)),F(0))/a[0])
    return tuple(b)
def sqrt_around_one(a):
    if a[0]!=1:raise ValueError("normalised ADM source required")
    out=[F(1)]
    for n in range(1,ORDER+1):
        out.append((a[n]-sum((out[k]*out[n-k] for k in range(1,n)),F(0)))/2)
    return tuple(out)
def diff(a):
    return trim([(i+1)*a[i+1] for i in range(ORDER)])
def coeff(a,k):return factorial(k)*a[k]

def dot(a,b):
    z=const(0)
    for x,y in zip(a,b):z=add(z,mul(x,y))
    return z

def make_source():
    # all time jets retain independent face and channel information.
    N=var(2,F(1,7),F(1,31))
    H=[var(1,F(i+1,17),F(i+2,137)) for i in range(4)]
    v=[var(F(i-1,13),F(i+1,29),F(i+3,101)) for i in range(4)]
    ft=var(F(1,11),F(2,31),F(-1,59))
    fx=[var(F(i-1,19),F(i+2,37),F(1,97)) for i in range(3)]
    Fspace=[neg(x) for x in fx]+[const(1)]
    Ftime=neg(ft)
    Hi=[reciprocal(x) for x in H]
    Ninv2=mul(reciprocal(N),reciprocal(N))
    det=const(1)
    for h in H:det=mul(det,h)
    D=mul(N,sqrt_around_one(det))
    theta=sub(Ftime,dot(v,Fspace))
    ktime=neg(mul(theta,Ninv2))
    kspace=[add(sub(mul(Hi[i],Fspace[i]),const(int(i==3))),
                mul(mul(theta,Ninv2),v[i])) for i in range(4)]
    assert any(c!=0 for c in ktime[1:])
    assert any(c!=0 for row in kspace for c in row[1:])
    return N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,ktime,kspace

def field_jet(ch,face,mu):
    return var(F((ch+2)*(face+3)*(mu+1)%23-11,11+mu),
               F((ch+4)*(face+1)*(mu+2)%29-14,17+mu),
               F((ch+7)*(face+2)*(mu+1)%31-15,29+mu))

def raw_flux(src,jet):
    N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
    derivative_time=jet[0]
    spatial=jet[1:]
    spatialflux=dot([mul(Hi[i],Fspace[i]) for i in range(4)],spatial)
    transport=sub(derivative_time,dot(v,spatial))
    return mul(D,sub(spatialflux,mul(mul(Ninv2,theta),transport)))

def canonical_graph_error(src,jet):
    N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
    normal=jet[4]
    error=mul(D,add(mul(kt,jet[0]),dot(ks,jet[1:])))
    return error,mul(D,normal)

def check_sector(sector):
    dim=15 if sector=="metric" else 5
    src=make_source()
    count=0
    for face in range(2):
        for ch in range(dim):
            jet=[field_jet(ch,face,mu) for mu in range(5)]
            raw=raw_flux(src,jet)
            error,base=canonical_graph_error(src,jet)
            assert raw==add(error,base),(sector,face,ch)
            # True higher-order Leibniz coefficients: derivative of
            # k(t)∂u(t) at order r is sum choose(r,a)k^(a) u^(r-a).
            N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
            pay=[mul(D,kt)]+[mul(D,x) for x in ks]
            for r in range(ORDER+1):
                want=sum((F(factorial(r),factorial(a)*factorial(r-a))
                          *coeff(pay[mu],a)*coeff(jet[mu],r-a)
                          for mu in range(5) for a in range(r+1)),F(0))
                assert want==coeff(error,r)
                # Explicit exact positive majorant, each scalar coefficient
                # paid independently; no unproved trace/energy reduction.
                major=sum((F(factorial(r),factorial(a)*factorial(r-a))
                          *abs(coeff(pay[mu],a))*abs(coeff(jet[mu],r-a))
                          for mu in range(5) for a in range(r+1)),F(0))
                assert abs(want)<=major
                count+=1
    print("PASS BR52",sector,dim,"channels, 2 faces, 9 orders, identities",count)
    print("PASS moving ADM D/N/H/v graph jets and exact full Leibniz error")

def negative():
    src=make_source()
    N,H,v,Hi,D,Ninv2,Fspace,Ftime,theta,kt,ks=src
    # A moving time graph or material normal shift is not a disposable
    # source. Construct independent contrasts against frozen F=n.
    assert ktime:=any(x!=0 for x in kt)
    jt=[field_jet(0,0,i) for i in range(5)]
    raw=raw_flux(src,jt)
    gaussian=mul(D,jt[4])
    assert raw!=gaussian
    # Frozen coefficient replacement would incorrectly miss the order-8
    # convolution. All exact higher source coefficients are retained.
    error,_=canonical_graph_error(src,jt)
    naive=add(mul(D,const(kt[0]*jt[0][0])),
              mul(D,const(sum(ks[i][0]*jt[i+1][0] for i in range(4)))))
    assert error!=naive
    print("PASS BR52 negative controls: moving time graph and 8th-order product non-erasure")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=("metric","gauge","negative","all"),default="all")
    a=p.parse_args()
    if a.part in ("metric","all"):check_sector("metric")
    if a.part in ("gauge","all"):check_sector("gauge")
    if a.part in ("negative","all"):negative()

if __name__=="__main__":main()
