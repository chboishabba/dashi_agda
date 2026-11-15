#!/usr/bin/env python3
"""B1 source U(1) 4-potential Maxwell field -> signed Poynting boundary.

Use Minkowski signature (-+++), F_mu_nu=dt_mu A_nu-dt_nu A_mu,
E_i=-F_0i, B=(F_23,F_31,F_12), J^nu=-partial_mu F^{mu nu}.
The explicit continuum C-infinity polynomial has nonzero charge/current.
This is NOT original measured SI boundary data or a physically calibrated
Maxwell medium. Source socket: U1ElectromagneticApplicationExact.agda.
"""
import sympy as s,json
from itertools import combinations

def check():
    t,x,y,z=s.symbols("t x y z",real=True)
    coords=(t,x,y,z)
    g=s.diag(-1,1,1,1)
    A=s.Matrix([0,t*(x*y+z*z),t*(y*z+x*x),t*(z*x+y*y)])
    F=s.Matrix(4,4,lambda i,j:
        s.diff(A[j],coords[i])-s.diff(A[i],coords[j]))
    assert F==-F.T
    chi=t*t*x*y+s.Rational(3,7)*z*z
    A_shift=A+s.Matrix([s.diff(chi,c) for c in coords])
    F_shift=s.Matrix(4,4,lambda i,j:
        s.diff(A_shift[j],coords[i])-s.diff(A_shift[i],coords[j]))
    assert F_shift==F
    for i,j,k in combinations(range(4),3):
        assert s.expand(s.diff(F[j,k],coords[i])
              +s.diff(F[k,i],coords[j])+s.diff(F[i,j],coords[k]))==0
    Fup=g*F*g
    J=s.Matrix([-sum(s.diff(Fup[mu,nu],coords[mu])
                     for mu in range(4)) for nu in range(4)])
    E=s.Matrix([-F[0,i] for i in (1,2,3)])
    B=s.Matrix([F[2,3],F[3,1],F[1,2]])
    assert B==s.Matrix([t*y,t*z,t*x])
    assert J==s.Matrix([-x-y-z,-t,-t,-t])
    assert s.expand(sum(s.diff(J[i],coords[i]) for i in range(4)))==0
    assert s.expand(J[0]-sum(s.diff(E[i],coords[i+1])
                             for i in range(3)))==0
    S=E.cross(B);u=(E.dot(E)+B.dot(B))/2
    work=J[1:4,0].dot(E)
    divS=sum(s.diff(S[i],coords[i+1]) for i in range(3))
    assert s.expand(s.diff(u,t)+divS+work)==0
    L=s.symbols("L",positive=True)
    integral=lambda f:s.integrate(f,(x,0,L),(y,0,L),(z,0,L))
    du=s.factor(integral(s.diff(u,t)))
    flux=s.factor(integral(divS))
    power=s.factor(integral(work))
    assert (du,flux,power)==(
        L**5*t,-s.Rational(11,4)*L**5*t,s.Rational(7,4)*L**5*t)
    return {
       "status":"PASS","formal_source_socket":"U1ElectromagneticApplicationExact",
       "metric":"(-+++)",
       "four_potential":[str(a) for a in A],
       "original_sourced_four_current":[str(a) for a in J],
       "antisymmetric_F":True,"all_four_Bianchi_identities":True,
       "gauge_transformed_F_identical":True,
       "charge_continuity":True,
       "original_4D_Maxwell_to_3D_Poynting":"PASS",
       "integrated_energy_time_rate":str(du),
       "integrated_outward_boundary_flux":str(flux),
       "integrated_current_electric_work":str(power),
       "source_PDE_continuum":"exact smooth polynomial, not arbitrary jets",
       "instrument_measured_SI_boundary":False
    }
if __name__=="__main__":print(json.dumps(check(),indent=2))
