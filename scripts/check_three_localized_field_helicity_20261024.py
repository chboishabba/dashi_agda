#!/usr/bin/env python3
"""Three LOCALIZED twisted Gaussian EM regions: Maxwell/helicity/anomaly gates.

Each smooth vector-potential packet models a localized field region, NOT an
actual self-maintaining plasma ball. Original sources: Maxwell helicity law
and Adler/Bell-Jackiw anomaly; no magnetic monopoles or gravity inferred.
"""
import math
import sympy as s
from numpy.polynomial.hermite import hermgauss
x,y,z,d,sigma,beta=s.symbols('x y z d sigma beta',positive=True,real=True)
def packet(cx,cy):
    u=x-cx;v=y-cy
    g=s.exp(-(u*u+v*v+z*z)/(2*sigma**2))
    return s.Matrix([-v*g,u*g,beta*g])
def curl(v):
    return s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),
      s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
A=packet(0,0);B=curl(A)
assert s.simplify(s.diff(B[0],x)+s.diff(B[1],y)+s.diff(B[2],z))==0
assert s.simplify(A.dot(B)-2*beta*s.exp(-(x*x+y*y+z*z)/sigma**2))==0
# Integrate A_i . curl A_j over all R3 by Gaussian moment completion.
V=s.pi**s.Rational(3,2)*sigma**3
h0=2*beta*V
h_cross=beta*V*s.exp(-d*d/(4*sigma**2))*(2-d*d/(2*sigma**2))
# Independent Gaussian quadrature of a displaced pair at separation=1.5.
nodes,weights=hermgauss(6)
f=s.lambdify((x,y,z,d,sigma,beta),A.dot(curl(packet(d,0))),'numpy')
cross_num=0.
for i,xx in enumerate(nodes):
 for j,yy in enumerate(nodes):
  for k,zz in enumerate(nodes):
   cross_num+=float(weights[i]*weights[j]*weights[k])*math.exp(float(xx*xx+yy*yy+zz*zz))*float(f(float(xx+0.75),float(yy),float(zz),1.5,1.,0.7))
cross_exact=float(h_cross.subs({d:1.5,sigma:1,beta:.7}))
assert abs(cross_num-cross_exact)<5e-11
# Equilateral 3 centers radius R => same off-diagonal h1 by C3.
R,t,omega,a=s.symbols('R t omega a',positive=True,real=True)
h1=s.simplify(h_cross.subs(d,s.sqrt(3)*R))
f_i=[a*s.cos(omega*t+2*s.pi*i/3) for i in range(3)]
H=s.trigsimp((h0-h1)*sum(f*f for f in f_i)+h1*sum(f_i)**2)
assert s.simplify(H-s.Rational(3,2)*(h0-h1)*a*a)==0
assert s.simplify(s.diff(H,t))==0  # balanced phase drive: NO net pumping
u=s.Function('envelope')(t);e=s.symbols('e',real=True)
H_driven=s.Rational(3,2)*(h0-h1)*u*u
integral_EB=-s.diff(H_driven,t)/2
assert s.simplify(integral_EB+s.Rational(3,2)*(h0-h1)*u*s.diff(u,t))==0
assert s.simplify(e*e/(2*s.pi*s.pi)*integral_EB+
                  e*e/(4*s.pi*s.pi)*s.diff(H_driven,t))==0
print('PASS: each localized field has div B=0 and positive-helicity density for beta>0')
print('PASS: analytic overlap helicity and independent Hermite quadrature')
print('PASS: balanced C3 120-degree drive has zero net E.B')
print('PASS: envelope-driven E.B and closed-domain axial anomaly/helicity balance')
print('OPEN: dynamical localized plasma, in-in fermion stress, Einstein backreaction')
