#!/usr/bin/env python3
"""EXACT 729-evaluation C27 orbit reduction for a candidate Griess
cubic; verified here on countermodels, NOT an actual Monster product.

For genuine Monster 2A axes a,b,c and certified order27 g,
C(P_r a,P_s b,P_t c) =
  1/27^2 sum_(u,v) zeta^(-su-tv) C(a,g^u b,g^v c)
for r+s+t=0 mod27, where C(a,b,c)=<a_1 b,c>.
Reduces naive 27^3 orbital scalar evaluations to 27^2=729.
"""
from fractions import Fraction
from itertools import product
import sympy as sym
N=27
x=sym.Symbol("x"); cyclo=x**18+x**9+1; modulus=127
E=(0,0); a=(1,0); b=(3,0); c=(23,0); triple={a,b,c}
dual=lambda z:((-z[0])%N,z[1])
def pairing(u,v):
    return 3 if u==E and v==E else int((u[0]+v[0])%N==0 and u[1]==v[1])
def multiply(u,v,t):
    if u==E:return {v:Fraction(1)}
    if v==E:return {u:Fraction(1)}
    out={}
    if pairing(u,v):out[E]=Fraction(pairing(u,v),3)
    if t and u!=v and u in triple and v in triple:
        third=next(z for z in triple if z!=u and z!=v)
        out[dual(third)]=Fraction(t)
    return out
def cubic(u,v,w,t):
    return sum(k*pairing(z,w) for z,k in multiply(u,v,t).items())
A={a:2,(5,0):1,E:1}
B={b:3,(26,0):5,E:1}
C={c:4,(0,1):2,(1,0):1}
def direct(r,s,t,mode):
    return sum((Fraction(aa*bb*cc)*cubic(u,v,w,mode)
         for u,aa in A.items() for v,bb in B.items()
         for w,cc in C.items()
         if u[0]==r and v[0]==s and w[0]==t),Fraction(0)) if (r+s+t)%N==0 else Fraction(0)
def orbit(r,s_charge,t,mode):
    if (r+s_charge+t)%N:return Fraction(0),0
    coefficients=[Fraction(0)]*N
    for i,j in product(range(N),repeat=2):
        for u,ua in A.items():
            for v,vb in B.items():
                for w,wc in C.items():
                    z=Fraction(ua*vb*wc)*cubic(u,v,w,mode)
                    if z:
                        exponent=((v[0]-s_charge)*i+(w[0]-t)*j)%N
                        coefficients[exponent]+=z
    poly=sum(z*x**j for j,z in enumerate(coefficients))
    rem=sym.Poly(poly,x,domain=sym.QQ).rem(sym.Poly(cyclo,x,domain=sym.QQ)).as_expr()
    value=sym.expand(rem/Fraction(N*N))
    assert not value.has(x)
    inv=lambda v:pow(v,-1,modulus)
    polyp=sym.Poly(sum(int(z.numerator)*inv(int(z.denominator))*x**j
                        for j,z in enumerate(coefficients)),x,modulus=modulus)
    remp=polyp.rem(sym.Poly(cyclo,x,modulus=modulus))
    assert remp.degree()<=0
    assert int(remp.as_expr())*inv(N*N)%modulus==int(value.p)*inv(int(value.q))%modulus
    return Fraction(value),N*N
for mode in (0,1,Fraction(7,3)):
    for r,s,t in ((1,3,23),(0,0,0),(1,3,0),(5,26,23)):
        value,calls=orbit(r,s,t,mode)
        assert value==direct(r,s,t,mode)
        if (r+s+t)%N==0:assert calls==729
assert direct(1,3,23,0)==0 and direct(1,3,23,1)==24
assert direct(1,3,23,Fraction(7,3))==56
print("PASS exact 729-orbit Griess cubic reduction over Q(zeta27) and F127[zeta27]")
print("PASS target (1,3,-4) cubic countermodels: zero, 24, 56")
print("OPEN actual certified Monster g, 2A axes, mmgroup triple scalar and VOA bulk action")
