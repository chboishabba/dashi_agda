#!/usr/bin/env python3
"""Full original KSW F8 TT tensor azimuthal norm, not scalar yy energy.

Original fourth-order projector owner retained:
T(k)=P(k) Q P(k)-P(k)tr(P(k)Q)/2; Q=diag(0,1,-1).
This check does not construct a full tensor radial-FV solution.
"""
import sympy as s

x,y,z,mu=s.symbols("x y z mu",real=True)
k=s.Matrix([x,y,z]); kk=k.dot(k)
P=kk*s.eye(3)-k*k.T
Q=s.diag(0,1,-1)
T=s.expand(P*Q*P-s.Rational(1,2)*P*s.trace(P*Q))
norm=s.expand(s.trace(T*T))
expected=s.Rational(1,2)*kk**2*((2*x*x+y*y+z*z)**2-4*y*y*z*z)
assert s.expand(norm-expected)==0

def azimuth_average(poly):
    out=s.S.Zero
    for (a,b,c),v in s.Poly(s.expand(poly),x,y,z).terms():
        if b%2 or c%2: continue
        i,j=b//2,c//2
        moment=s.factorial(2*i)*s.factorial(2*j)/(4**(i+j)*s.factorial(i)*s.factorial(j)*s.factorial(i+j))
        out+=v*mu**a*(1-mu**2)**(i+j)*moment
    return s.factor(out)

av=azimuth_average(norm)
assert s.simplify(av-(mu**4+6*mu**2+1)/4)==0
assert s.simplify(2*azimuth_average(T[1,1])-av)==0
assert s.integrate(av,(mu,-1,1))==s.Rational(8,5)
for ell,val in {0:s.Rational(4,5),2:s.Rational(8,7),4:s.Rational(2,35),6:0,8:0}.items():
    c=s.Rational(2*ell+1,2)*s.integrate(av*s.legendre(ell,mu),(mu,-1,1))
    assert s.simplify(c-val)==0
assert norm.subs({x:0,y:1,z:0})==s.Rational(1,2)
assert norm.subs({x:0,y:s.Rational(3,5),z:s.Rational(4,5)})==s.Rational(49,1250)
phi=s.symbols("phi",real=True)
ring=s.trigsimp(norm.subs({x:mu,y:s.sqrt(1-mu**2)*s.cos(phi),z:s.sqrt(1-mu**2)*s.sin(phi)}))
remainder=av+(1-mu**2)**2*s.cos(4*phi)/4
assert s.trigsimp(s.expand_trig(ring-remainder))==0
print("12/12 exact original full-tensor Fourier angular tests PASS")
print("Azimuthal average:",av)
print("Azimuthal remainder: (1-mu^2)^2 cos(4 phi)/4")
