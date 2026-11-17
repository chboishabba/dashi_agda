#!/usr/bin/env python3
"""F10/F13 selected-model bridge; not measured same-original Maxwell access.

Source attribution: classical Poynting, Debye auxiliary-variable energy,
ionospheric Hall/Pedersen conductivity; ideal electrostatic half-space
spreading (not general plate/soil/ionosphere 3D solution).
Reuse PR #1521 SmithFilsingerDispersiveMaterialPortExact and
check_smith_filsinger_earth_admittance_access.py.
Original Smith/Filsinger solar coupling and timed source/sink = user-origin
conditional hypothesis. External cited work is not a device validation.
"""
import json
import math
from dataclasses import dataclass
import sympy as s

def f10_debye_modulation():
    t=s.symbols('t',real=True)
    eps,tau=s.symbols('eps tau',positive=True)
    P=s.Function('P')(t); chi=s.Function('chi')(t); E=s.Function('E')(t)
    D=eps*E+P
    U=eps*E**2/2+P**2/(2*eps*chi)
    Pdot=s.diff(P,t); chidot=s.diff(chi,t)
    EfromADE=(tau*Pdot+P)/(eps*chi) # tau*Pdot+P=eps*chi*E
    modulation_input=-P**2*chidot/(2*eps*chi**2)
    dissipation=tau*Pdot**2/(eps*chi)
    assert s.simplify((E*s.diff(D,t)+modulation_input-s.diff(U,t)-dissipation).subs(E,EfromADE))==0
    epsilon=s.Function('epsilon')(t)
    assert s.simplify(E*s.diff(epsilon*E,t)-s.diff(epsilon*E**2/2,t)-s.diff(epsilon,t)*E**2/2)==0
    return True

def f10_hall_pedersen():
    Ex,Ey,Ez,sp,sh,sz,vx,vy,B=s.symbols('Ex Ey Ez sigmaP sigmaH sigmaParallel vx vy B',real=True)
    Ep=(Ex-vy*B,Ey+vx*B,Ez)
    J=(sp*Ep[0]-sh*Ep[1],sp*Ep[1]+sh*Ep[0],sz*Ep[2])
    neutral=sum(a*b for a,b in zip(Ep,J))
    assert s.expand(neutral-sp*(Ep[0]**2+Ep[1]**2)-sz*Ep[2]**2)==0
    lab=Ex*J[0]+Ey*J[1]+Ez*J[2]
    assert s.expand(lab-neutral+(vx*B*J[1]-vy*B*J[0]))==0
    return True

def f10_poynting_local():
    # From -outgoing_flux = Jfree.E + E.Ddot + H.Bdot,
    # E.Ddot + signed_material_mod_input = dUelectric_memory/dt + loss.
    ed,hb,j,ud,loss,mod=s.symbols('ED HB J Udot loss mod')
    flux=-j-ed-hb
    assert s.expand(flux.subs(ed,ud+loss-mod)+j+ud+loss+hb-mod)==0
    return True

@dataclass(frozen=True)
class HalfSpaceCollector:
    sigma_air:float=1e-14
    radius_m:float=1.
    potential_v:float=100.
    def conductance(self):
        assert self.sigma_air>0 and self.radius_m>0
        return 2*math.pi*self.sigma_air*self.radius_m
    def spread_resistance(self):return 1/self.conductance()
    def current(self):return self.potential_v*self.conductance()
    def ideal_disk_contact_g(self):return 4*self.sigma_air*self.radius_m
    def hypothetical_thevenin_matched_w(self,voc):return voc**2*self.conductance()/4

def f13_halfspace_laplace():
    r,a,v,sigma=s.symbols('r a V sigma',positive=True)
    phi=v*a/r # hemisphere electrode, insulated plane elsewhere
    assert s.simplify(s.diff(r*r*s.diff(phi,r),r)/r**2)==0
    assert s.simplify(-sigma*s.diff(phi,r)*2*s.pi*r*r-2*s.pi*sigma*v*a)==0
    return True

def f13_fixed_column():
    z,h,sigma0,H,A=s.symbols('z h sigma0 H A',positive=True)
    R=s.integrate(s.exp(-z/H)/(A*sigma0),(z,0,h))
    assert s.simplify(R-H*(1-s.exp(-h/H))/(A*sigma0))==0
    return True

def run():
    checks={'F10_Debye_modulator':f10_debye_modulation(),
            'F10_Hall_neutral_frame':f10_hall_pedersen(),
            'F10_Poynting_partition':f10_poynting_local(),
            'F13_hemispherical_Laplace':f13_halfspace_laplace(),
            'F13_fixed_area_stratified_column':f13_fixed_column()}
    m=HalfSpaceCollector()
    assert all(checks.values())
    return {'checks':checks,'selected_hemisphere_R_ohm':m.spread_resistance(),
            'selected_hemisphere_G_S':m.conductance(),
            'ideal_disk_boundary_G_S':m.ideal_disk_contact_g(),
            'hypothetical_200V_thevenin_Pmatched_W':m.hypothetical_thevenin_matched_w(200.),
            'F10_scope':'selected local Debye ADE; instant epsilon; Hall neutral-frame; Maxwell field identity, NOT solved 3D PDE',
            'F13_scope':'exact homogeneous hemispherical half-space benchmark and independent 1D stratified column, NOT exact multilayer collector/ionosphere source or measured Voc',
            'open':['actual air/soil interface', '3D stratified Hall/Pedersen ionosphere, causal Green field','actual natural open and loaded V-I','source replenishment and signed work']}

if __name__=='__main__':print(json.dumps(run(),indent=2))
