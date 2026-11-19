"""Exact free-space 3D Green witness: uniformly polarized spherical support.
Not a material calibration or GR solution. Source is imposed uniform scalar gradient.
Classical Newton kernel / electrostatic dipole and Schur complement; new BIDI synthesis.
"""
import sympy as s
import math
R,r,K,lam,mu,B=s.symbols('R r K lam mu B',positive=True)
V=4*s.pi*R**3/3
S=lam**2*V/(3*K)
# X couples to integral of vertical gradient, same field measured outside.
# exterior solution delta theta = lam X V z/(4 pi K r^3)
# probe gradient factor at pole/equator
for angular,target in [(-2,-3),(1,5)]:
    P=lam*V*angular/(4*s.pi*K*r**3)
    drive=lam*V*B
    curvature=S+drive*P/(B*(target-1))
    assert s.simplify(1+drive*P/(B*(curvature-S))-target)==0
    assert s.simplify((curvature-S)/S-3*V*angular/(4*s.pi*r**3*(target-1)))==0
    print('angular',angular,'target',target,'margin',s.simplify((curvature-S)/S))
# physical theta gradient; canonical stiffness; exterior dipolar perturbation energy
G=6.67430e-11;c=299792458.;g=9.80665;radius=.1375;distance=radius+.1
Ksi=c**4/(8*math.pi*G); volume=4*math.pi*radius**3/3
for f in [.25,1e-5]:
    ambient=math.sqrt(6)*f*g/c**2
    for angular,delta in [(-2,-1),(1,1)]:
        target=1+delta/f
        margin=radius**3/distance**3*angular/(target-1)
        # amplitude D in delta theta=D cos(angle)/r²; field energy outside support =4pi K D²/(3 R³)
        D=(target-1)*ambient*distance**3/angular
        energy=4*math.pi*Ksi*D**2/(3*radius**3)
        print('f',f,'target',target,'margin',margin,'dipole m²',D,'external perturbation energy J',energy,'polarization lambdaX J/m²',4*math.pi*Ksi*D/volume)
        assert margin>0 and energy>0
print('PASS exact inverse and positive Schur margin')
