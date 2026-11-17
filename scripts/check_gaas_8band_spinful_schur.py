#!/usr/bin/env python3
"""Symbolic near-Gamma 8-state Kane S/X/Y/Z spinful Schur complement.
Spinless orbital C3v is NOT this spinful Hamiltonian, nor PV proof.
Gamma8 4-fold at 0, Gamma7 2-fold at -Delta, Gamma6 2-fold at Eg.
The remote-band parameter F is a curvature term, not an explicit band.
"""
import sympy as s
import numpy as np
import json

i=s.I
Lx=s.Matrix([[0,0,0],[0,0,-i],[0,i,0]])
Ly=s.Matrix([[0,0,i],[0,0,0],[-i,0,0]])
Lz=s.Matrix([[0,-i,0],[i,0,0],[0,0,0]])
Sx=s.Matrix([[0,1],[1,0]])/2
Sy=s.Matrix([[0,-i],[i,0]])/2
Sz=s.diag(1,-1)/2
LdotS=sum((s.kronecker_product(L,S) for L,S in
           zip((Lx,Ly,Lz),(Sx,Sy,Sz))),s.zeros(6))
gap,delta,Ep=s.symbols("Eg Delta Ep",positive=True)
F=s.symbols("F",real=True)
kx,ky,kz=s.symbols("kx ky kz",real=True)
k2=kx*kx+ky*ky+kz*kz
Hv=s.Rational(2,3)*delta*LdotS-delta*s.eye(6)/3
B=s.zeros(2,6)
for orb,k in enumerate((kx,ky,kz)):
    for spin in range(2):
        B[spin,2*orb+spin]=k
C=s.sqrt(Ep)*B
Hc=(gap+(1+2*F)*k2)*s.eye(2)
H=Hc.row_join(C).col_join(C.T.row_join(Hv))

tests=[]
def check(name,yes):
    assert bool(yes),name
    tests.append(name)

check("Gamma8/Gamma7 spectrum",Hv.eigenvals()=={s.Integer(0):4,-delta:2})
check("8x8 dimension",H.shape==(8,8))
check("Hermiticity",all(s.simplify(x)==0 for x in H-H.H))
res=s.simplify(B*(gap*s.eye(6)-Hv).inv()*B.T)
coef=s.Rational(2,3)/gap+s.Rational(1,3)/(gap+delta)
check("Schur effective coupling isotropic",
      all(s.simplify(x)==0 for x in res-coef*k2*s.eye(2)))
inv_mass=s.simplify(1+2*F+Ep*coef)
check("agrees source formula",
      s.simplify(inv_mass-(1+2*F+Ep/3*(2/gap+1/(gap+delta))))==0)

mass={}
for temperature,energy_gap in (("0K",s.Rational(1519,1000)),
                               ("300K",s.Rational(1422,1000))):
    parameters={gap:energy_gap,delta:s.Rational(341,1000),
                Ep:s.Rational(288,10),F:-s.Rational(194,100)}
    desired=float(inv_mass.subs(parameters))
    mass[temperature]=1/desired
    for axis_name,axis in (("100",(1,0,0)),("010",(0,1,0)),
                           ("001",(0,0,1)),("111",(1/np.sqrt(3),)*3)):
        kinetic_eV=1e-7
        vals=dict(parameters)
        vals.update({kx:np.sqrt(kinetic_eV)*axis[0],
                     ky:np.sqrt(kinetic_eV)*axis[1],
                     kz:np.sqrt(kinetic_eV)*axis[2]})
        spectrum=np.linalg.eigvalsh(np.asarray(H.subs(vals).evalf(),
                                               dtype=complex))
        numerical=(spectrum[-1]-float(energy_gap))/kinetic_eV
        check(temperature+" "+axis_name+" numeric 8x8 curvature",
              abs(numerical-desired)<1e-4)
    check(temperature+" electron inverse mass positive",desired>10)
check("0K near 0.067m0",abs(mass["0K"]-.067)<1e-4)
check("300K fixed F near 0.06224m0",abs(mass["300K"]-.062238)<1e-4)

receipt={"all_passed":True,"check_count":len(tests),
         "spinful_8state_model":"S spin 2 + xyz spin 6, SO splitting, F effective remote curvature",
         "Schur_inverse_effective_mass":str(inv_mass),
         "mass_over_m0":mass,
         "NO_real_material_BirPikus_or_PV_gain_proven":True,
         "checks":tests}
print(json.dumps(receipt,indent=2))
