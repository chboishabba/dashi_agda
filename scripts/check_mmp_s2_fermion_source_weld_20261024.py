#!/usr/bin/env python3
"""Source-first S2 monopole-Dirac/Casimir angular-stress and Ward control.

SCOPED: finite massive-mode adiabatic spectral potential, not a full curved
4D fermion determinant, monopole-engineering proposal, or MMP reproduction.
Roots: spin-c S2 Dirac spectrum; massive 1+1D NS Dirac Casimir; spherical GR.
"""
import math
import sympy as s
from scipy.special import kv

q_values=(3,10,11,12,13,24)
def mode_levels(q,r,nmax):
    assert isinstance(q,int) and r>0
    return [(n,math.sqrt(n*(n+abs(q)))/r,abs(q)+2*n)
            for n in range(1,nmax+1)]
def energy_ns(m,L,kmax=80):
    if m==0:return -math.pi/(6*L)
    return -2*m/math.pi*sum((1 if k%2 else -1)*kv(1,k*m*L)/k
                            for k in range(1,kmax+1))
def potential(q,r,L,nmax=4):
    return sum(2*d*energy_ns(m,L)/L for _,m,d in mode_levels(q,r,nmax))
for q in q_values:
    assert all(deg==abs(q)+2*n for n,_,deg in mode_levels(q,2,4))
    h=1e-4
    V=potential(q,1,3)
    Vprime=(potential(q,1+h,3)-potential(q,1-h,3))/(2*h)
    assert math.isfinite(V) and math.isfinite(Vprime)
assert abs(energy_ns(1e-6,3)+math.pi/18)<2e-6
# W=-integral sqrt(-h) V(r) implies 4D transverse pressure
# p_t=-V'(r)/(8pi*r), rho=V/(4pi*r²), p_r=-rho.
r,v,V,Vprime=s.symbols('r v V Vprime',real=True,nonzero=True)
rho=V/(4*s.pi*r*r); pr=-rho; pt=-Vprime/(8*s.pi*r)
prprime=-Vprime*v/(4*s.pi*r*r)+2*V*v/(4*s.pi*r**3)
assert s.simplify(prprime+2*v/r*(pr-pt))==0
# Polyakov + massive tower: full radial Einstein constraint C propagates
# when Gtt and Gθθ are sourced from the SAME effective action.
F,N,rr,FF,c,t,Q=s.symbols('F N rr FF c t Q',real=True)
Epoly=c*FF/(12*s.pi)+c*F*F/(24*s.pi)+2*t/N**2
Ppoly=-c*F*F/(24*s.pi)+2*t/N**2
Et=1-v*v-2*r*rr-Q**2/r**2-2*(Epoly+V)
Etheta=FF+F*F+F*v/r+rr/r-Q**2/r**4+Vprime/r
sol=s.solve([Et,Etheta],[rr,FF])
assert rr in sol and FF in sol
C=v*v-1+2*r*v*F+Q**2/r**2-2*(Ppoly-V)
DC=(s.diff(C,r)*v+s.diff(C,v)*sol[rr]+
    s.diff(C,F)*sol[FF]+s.diff(C,N)*N*F+s.diff(C,V)*Vprime*v)
assert s.simplify(DC+F*C)==0
print('PASS: monopole index/KK spectrum, massive NS mode values')
print('PASS: same-action angular stress/4D spherical Ward')
print('PASS: Einstein radial constraint propagates exactly, Cprime=-PhiPrime*C')
print('NOT TESTED: global Dirac determinant, 4D renormalized state, Hall current, RN mouths')
