#!/usr/bin/env python3
"""Exact original KSW F8 Cartesian TT fourth derivative -> radial mode source.

Differential-jet proof independently reuses the ORIGINAL TT polynomial,
Legendre P0/P2/P4 source profiles and finite-volume endpoint primitives.
This is not a discrete tensor FV evolution, Agda kernel or physical proof.
"""
import sympy as s
x,y,z,r,mu=s.symbols("x y z r mu",real=True)
kx,ky,kz=s.symbols("kx ky kz")
k=s.Matrix([kx,ky,kz]);P=k.dot(k)*s.eye(3)-k*k.T
Q=s.diag(0,1,-1)
T=(P*Q*P-P*s.trace(P*Q)/2).applyfunc(s.expand)
op=kx**4+s.Rational(1,2)*kx**2*ky**2+s.Rational(3,2)*kx**2*kz**2-s.Rational(1,2)*ky**2*kz**2+s.Rational(1,2)*kz**4
assert s.expand(T[1,1]-op)==0
checks=1
# Chain rule for the fourth derivatives of a radial function
# f(r)=F((x²+y²+z²)/2). Its radial derivatives are D^n f.
u=(x*x+y*y+z*z)/2
f=s.Function("F")(u)
expr=s.Integer(0)
for (a,b,c),coef in s.Poly(op,kx,ky,kz).terms():
    expr+=coef*s.diff(f,x,a,y,b,z,c)
D=s.symbols("D0:5")
expr=expr.replace(
    lambda e:isinstance(e,s.Subs) and isinstance(e.expr,s.Derivative) and e.expr.expr.func==s.Function("F"),
    lambda e:D[len(e.expr.variables)])
expr=s.expand(expr)
assert s.expand(expr-(6*D[2]+(8*x*x+4*z*z)*D[3]+op.subs({kx:x,ky:y,kz:z})*D[4]))==0
checks+=1

def azavg(poly):
    ans=s.S.Zero
    for (i,j),c in s.Poly(s.expand(poly),y,z).terms():
        if i%2 or j%2:continue
        a,b=i//2,j//2
        moment=s.factorial(2*a)*s.factorial(2*b)/(4**(a+b)*s.factorial(a)*s.factorial(b)*s.factorial(a+b))
        ans+=c*(r*r-x*x)**(a+b)*moment
    return s.expand(ans)

a=(mu**4+6*mu**2+1)/8
assert s.simplify(azavg(expr).subs(x,r*mu)-(6*D[2]+(2+6*mu**2)*r*r*D[3]+a*r**4*D[4]))==0
checks+=1
p0=1;p2=s.legendre(2,mu);p4=s.legendre(4,mu)
assert s.expand(2+6*mu**2-(4*p0+4*p2))==0;checks+=1
assert s.expand(a-(s.Rational(2,5)*p0+s.Rational(4,7)*p2+s.Rational(1,35)*p4))==0;checks+=1
f1,f2,f3,f4=s.symbols("f1 f2 f3 f4")
j2=r*r*f2-r*f1
j3=r**3*f3-3*r*r*f2+3*r*f1
j4=r**4*f4-6*r**3*f3+15*r*r*f2-15*r*f1
modes={0:6*j2+4*j3+s.Rational(2,5)*j4,
       2:4*j3+s.Rational(4,7)*j4,4:s.Rational(1,35)*j4}
profiles={0:s.Rational(2,5)*(r**4*f4+4*r**3*f3),
          2:s.Rational(4,7)*(r**4*f4+r**3*f3-6*r*r*f2+6*r*f1),
          4:s.Rational(1,35)*(r**4*f4-6*r**3*f3+15*r*r*f2-15*r*f1)}
for ell in modes:
    assert s.expand(modes[ell]-profiles[ell])==0
    checks+=1
t=s.symbols("t",positive=True);h=s.Function("f")(t);der=[h]+[s.diff(h,t,i) for i in range(1,5)]
primitives={0:s.Rational(2,5)*(t*t*der[3]+2*t*der[2]-2*der[1]),
  2:s.Rational(4,7)*(t**4*der[3]-3*t**3*der[2]+3*t*t*der[1]),
  4:(t**6*der[3]-12*t**5*der[2]+75*t**4*der[1]-315*t**3*h)/35}
for ell in modes:
    weighted=s.expand(profiles[ell].subs({r:t,f1:der[1],f2:der[2],f3:der[3],f4:der[4]})*t**(ell-2))
    remainder=27*t*t*h if ell==4 else 0
    assert s.simplify(s.diff(primitives[ell],t)+remainder-weighted)==0
    checks+=1
assert s.expand(modes[0]-s.Rational(2,5)*j4)!=0
assert s.expand(modes[2]-s.Rational(4,7)*j4)!=0
checks+=2
# Exact origin-safe source-weight transport to actual original FV primitives.
weighted={0:s.Rational(2,5)*(r*r*f4+4*r*f3),
  2:s.Rational(4,7)*(r**4*f4+r**3*f3-6*r*r*f2+6*r*f1),
  4:(r**6*f4-6*r**5*f3+15*r**4*f2-15*r**3*f1)/35}
assert s.expand(r*r*weighted[0]-modes[0])==0;checks+=1
assert s.expand(weighted[2]-modes[2])==0;checks+=1
assert s.expand(weighted[4]-r*r*modes[4])==0;checks+=1
print(f"{checks}/{checks} original Cartesian TT radial differential / source primitive tests PASS")
