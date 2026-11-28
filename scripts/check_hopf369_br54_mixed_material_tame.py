#!/usr/bin/env python3
"""BR54: geometry-forward mixed tangential/normal physical graph source.

The actual Gaussian ADM special case N=2,H=I,v=0,D=2, moving material
F=n-f(t,x,y,z) has
    J_F(u)-2 u_n = 2[(f_t/4)u_t - f_x u_x-f_y u_y-f_z u_z].
Its derivatives through arbitrary tangential multi-index alpha are the
full multinomial Leibniz product, not merely time-jet BR52.

The exact finite identity is accompanied by the real/Hermitian majorant
    |D^alpha(k·du)| <= sum_{beta<=alpha} binom(alpha,beta)
                        |D^beta k| |D^(alpha-beta)du|
and uniform upper bound 2^|alpha| K_s U_s where *independent*
higher source regularity K_s,U_s is required.

The original 15+5 channels remain separate. This does not prove
physical global weighted Sobolev product inequalities, BR37 glancing
bounds, normal derivative absorption, or the nonlinear source estimate.
"""
from itertools import product
from math import comb
from fractions import Fraction as F
import argparse
import sympy as s

coords=s.symbols("t x y z")
n=s.Symbol("n")
def deriv(f,alpha):
    for x,k in zip(coords,alpha):
        if k:f=s.diff(f,x,k)
    return f
def subalpha(alpha):
    return product(*[range(a+1) for a in alpha])
def binom(alpha,beta):
    q=1
    for a,b in zip(alpha,beta):q*=comb(a,b)
    return q

def graph():
    t,x,y,z=coords
    # This polynomial is a non-flat moving material graph with all
    # four-dimensional mixed jets, including an eighth-order time mode.
    f=(t**5*x**2/7 + x*y*z/5 + t*x*y/11 +
       t**8*z/23 + y**5*z/17 + x**4*t**3/31)
    k=[s.diff(f,t)/4,-s.diff(f,x),-s.diff(f,y),-s.diff(f,z)]
    assert all(q!=0 for q in k)
    return f,k

def field(ch):
    t,x,y,z=coords
    return (s.Rational(ch+1,7)*t**3*x*n
        +s.Rational(ch+3,11)*x**2*y*z
        +s.Rational(ch+5,13)*t*y**3
        +s.Rational(ch+7,17)*t**2*z*n**2
        +s.Rational(ch+9,19)*x*z**2)

def check(sector,alpha):
    rank=15 if sector=="metric" else 5
    f,k=graph()
    tested=0
    for ch in range(rank):
        u=field(ch)
        jet=[s.diff(u,q) for q in coords]
        physical=2*sum(k[i]*jet[i] for i in range(4))
        direct=deriv(physical,alpha)
        split=2*sum(
            binom(alpha,beta)*sum(
                 deriv(k[i],beta)*deriv(jet[i],
                    tuple(a-b for a,b in zip(alpha,beta)))
                 for i in range(4))
            for beta in subalpha(alpha))
        assert s.expand(direct-split)==0,(sector,ch,alpha)
        # Fixed normal density D=2 reference: sign of moving
        # time-tilt is positive f_t/4 and spatial signs negative.
        current=2*(s.diff(u,n)+s.diff(f,t)*s.diff(u,coords[0])/4
                      -sum(s.diff(f,coords[i])*s.diff(u,coords[i])
                           for i in range(1,4)))
        assert s.expand(current-2*s.diff(u,n)-physical)==0
        # Exact rational positive evaluation at an inhabited graph point.
        at={coords[i]:s.Rational(i+2,7) for i in range(4)}
        at[n]=s.Rational(3,5)
        lhs=s.cancel(direct.subs(at))
        # The square/triangle estimate is paid by individual terms:
        payment=sum(
            binom(alpha,beta)*sum(
                abs(s.cancel((2*deriv(k[i],beta)*
                 deriv(jet[i],tuple(a-b for a,b in zip(alpha,beta)))).subs(at)))
                for i in range(4))
            for beta in subalpha(alpha))
        assert abs(lhs)<=payment
        tested+=1
    print("PASS BR54",sector,"rank",rank,"multi-index",alpha,
          "full physical mixed-product/source identities",tested)

def negative():
    f,k=graph();u=field(4);t,x,y,z=coords
    # Discarding the moving time graph is NOT harmless.
    assert s.diff(f,t)*s.diff(u,t)!=0
    # Discarding mixed tangential wall derivatives is NOT harmless.
    alpha=(2,2,1,0)
    correct=deriv(2*sum(k[i]*s.diff(u,coords[i]) for i in range(4)),alpha)
    naive=2*sum(k[i]*deriv(s.diff(u,coords[i]),alpha) for i in range(4))
    assert s.expand(correct-naive)!=0
    # An independent high-order positive trace source cannot be inferred
    # from the original order-zero BR4 energy.
    print("PASS BR54 negative controls: time-moving graph and mixed Leibniz debt")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=["metric","gauge","negative"],required=True)
    p.add_argument("--multi",default="2,2,2,2")
    a=p.parse_args()
    if a.part=="negative":negative();return
    alpha=tuple(map(int,a.multi.split(",")))
    if len(alpha)!=4 or min(alpha)<0 or sum(alpha)>8:raise ValueError(alpha)
    check(a.part,alpha)

if __name__=="__main__":main()
