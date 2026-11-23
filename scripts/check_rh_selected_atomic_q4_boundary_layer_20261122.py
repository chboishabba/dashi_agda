#!/usr/bin/env python3
"""Exact moving q=4 boundary layer for the original four-window ATOMIC kernel.

Local SymPy regression only; not the selected positive-width W and not zeta-zero data.
At u=pi/t, a=beta-1/2, q=4+z*u, proves the u^0..u^3
coefficients vanish and computes the u^4 coefficient exactly.
"""
import sympy as s

F=s.Rational
u,a,z=s.symbols("u a z",real=True)
centres=(s.Integer(0),F(1,3),F(1,2),s.Integer(1))
mu=lambda L:(13*L-8)/(144-54*L)
A1=lambda L:F(1,2)-mu(L)
A2=lambda L:F(3,2)-L+mu(L)
weights=lambda L:(s.Integer(1),s.Integer(-1),L,mu(L))
q=4+z*u

def poly4(x):
    return s.series(x,u,0,5).removeO().expand()

def profile(L):
    return s.expand(4*sum(
        w*(A1(L)*s.cos(2*s.pi*c)-A2(L)*s.cos(s.pi*c))
        *poly4(s.cos(s.pi*q*c))*poly4(s.cosh(16*a*c*u))
        for w,c in zip(weights(L),centres)))

def pole(L):
    h1=poly4(s.cosh(F(8,3)*u))
    h2=poly4(s.cosh(4*u))
    h3=poly4(s.cosh(8*u))
    return s.expand((1+h1/4-mu(L)*h3)*A2(L)
                    -(1-h1/4-L*h2+mu(L)*h3)*A1(L))

K=s.Poly(s.expand(pole(F(2,3))*profile(F(1,2))
                  -pole(F(1,2))*profile(F(2,3))),u)
for j in range(4):
    assert K.nth(j)==0
C=s.factor(K.nth(4))
expected=F(5,1404)*(4096-65536*a**4
                     +1536*s.pi**2*a**2*z**2-s.pi**4*z**4)
assert s.simplify(C-expected)==0
assert s.factor(C.subs(z,0)-F(5120,351)*(1-16*a**4))==0
# |z| < zcrit is exactly the positive leading-coefficient interval
# for fixed |a|<1/2, with zcrit=8/pi*sqrt(12a^2+sqrt(1+128a^4)).
zcrit2=64/s.pi**2*(12*a**2+s.sqrt(1+128*a**4))
assert s.simplify(expected.subs(z**2,zcrit2))==0
assert s.factor((768*a**2)**2-(64**2)*(1+128*a**4))==4096*(2*a-1)*(2*a+1)*(4*a*a+1)
# Physical delta gamma=(t/16)*(q-4)=pi*z/16: fixed-scale width.
assert s.simplify((s.pi/16)**2*zcrit2
                  -F(1,4)*(12*a*a+s.sqrt(1+128*a**4)))==0
print("PASS: exact u^0..u^3 cancellation and moving q=4 fourth coefficient")
print("PASS: q=4 recovery, exact boundary roots, physical ordinate width")
print("OPEN: positive-R selected W and actual-zero signed terminal with slack")
