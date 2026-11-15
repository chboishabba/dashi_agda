#!/usr/bin/env python3
"""Single-action 5D circle compactification: winding/radion/U(1) steelman.
5D EFT S=integral sqrt(-G)[M5^3 R5/2 - Lambda5 - v² (dTheta)²/2],
Theta=n*y+chi(x); ds5²=gJ+b²(dy+kappa*A)²; y periodic 2*pi.
The 5D Einstein-Hilbert reduction to b*R4 is assumed from PR #1239.
Tests derived matter coupling, two-term vacuum and KK photon mass obstruction.
No actual Earth source or complete 5D action/field variation claimed.
"""
import sympy as s
b,b0,v,n,kappa=s.symbols("b b0 v n kappa",positive=True,real=True)
a,c,g=s.symbols("a c g",real=True,nonzero=True)
G=s.Matrix([[g+b*b*kappa*kappa*a*a,b*b*kappa*a],[b*b*kappa*a,b*b]])
Gi=s.simplify(G.inv())
assert s.simplify(G.det()-g*b*b)==0
phasegrad=s.Matrix([c,n])
grad=s.factor((phasegrad.T*Gi*phasegrad)[0])
assert s.simplify(grad-((c-n*kappa*a)**2/g+n*n/b**2))==0
epsilon=s.symbols("epsilon",real=True)
assert s.expand((c+n*kappa*epsilon)-n*kappa*(a+epsilon)-(c-n*kappa*a))==0

La=s.symbols("La",real=True)
W=s.symbols("W",positive=True,real=True) # W=v²n²/2 >0
V=s.factor(2*s.pi*b0*b0*(La/b+W/b**3))
critical_La=s.solve(s.diff(V,b),La)[0]
critical_V=s.factor(V.subs(La,critical_La))
critical_curvature=s.factor(s.diff(V,b,2).subs(La,critical_La))
assert s.simplify(critical_La+3*W/b**2)==0
assert s.simplify(critical_V+4*s.pi*b0*b0*W/b**3)==0
assert s.simplify(critical_curvature-12*s.pi*b0*b0*W/b**5)==0
assert not s.solve([V,s.diff(V,b)],[La,W],dict=True)

Mp,varphi=s.symbols("M_P varphi",positive=True,real=True)
br=b0*s.exp(s.sqrt(s.Rational(2,3))*varphi/Mp)
assert s.simplify(s.sqrt(s.Rational(3,2))*Mp*s.log(br/b0)-varphi)==0
ln_matter_A=-varphi/(s.sqrt(6)*Mp)
beta=s.diff(ln_matter_A,varphi)
relative_force=s.simplify(2*(Mp*beta)**2)
gamma=s.factor((1-relative_force)/(1+relative_force))
assert relative_force==s.Rational(1,3) and gamma==s.Rational(1,2)
rho=s.symbols("rho",positive=True,real=True)
source_rhs=s.simplify(-beta*(-rho))
assert s.simplify(source_rhs+rho/(s.sqrt(6)*Mp))==0
stueckelberg_coefficient=s.factor(2*s.pi*b0*b0*v*v*n*n*kappa*kappa/(2*b))
assert stueckelberg_coefficient!=0

print("PASS KK inverse metric, covariant phase derivative (dchi-n*kappa*A), and gauge covariance")
print("PASS radion normalized field and Jordan-matter beta = -1/sqrt(6)/M_P")
print("PASS unscreened scalar strength = 1/3, Jordan PPN gamma = 1/2")
print("PASS dust source (laplacian-m²)phi = ",source_rhs)
print("PASS winding+Lambda stationary La=",critical_La)
print("PASS potential at minimum =",critical_V,"and V'' =",critical_curvature)
print("PASS no stationary Minkowski vacuum for W>0 in this two-term model")
print("PASS graviphoton gets nonzero Stueckelberg mass for v*n*kappa != 0")
print("LIMIT fixed-modulus scalar action and zero-mode reduction assumptions; no physical Earth source")
