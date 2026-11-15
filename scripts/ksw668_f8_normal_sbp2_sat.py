#!/usr/bin/env python3
"""Original moving a=t AdS5 second-order SBP+SAT Neumann normal transport.

Trapezoidal H=diag(dy/2,dy,...,dy,dy/2), centred 2nd-order interior
D, and 1st-order one-sided endpoint D satisfy exact 2<u,Du>_H
=u_far²-u_wall². Characteristic SAT acts at incoming boundaries:
 P_t=(1+v)DP - (1+v)/H_far P_far e_far,
 M_t=(v-1)DM + (1-v)/H_wall (Mtarget-Mwall)e_wall,
 Mtarget=beta Pwall-2G/(1-v).
Then exact weighted semidiscrete normal energy derivative
=Fwall-(1+v)Pfar²-(1-v)Mfar²-(1-v)(Mwall-Mtarget)²
<=2sqrt5 G², original t in [1,2].
NOTE: weak SAT boundary, NOT pointwise Israel enforcement; the full
coupled RK3 radial/warp/Weyl theorem remains OPEN.
"""
import json,math
import numpy as np
def derivative(u,dy=1.):
    u=np.asarray(u,float)
    if u.ndim!=1 or len(u)<3 or dy<=0:raise ValueError('finite SBP normal mesh')
    out=np.empty_like(u)
    out[0]=(u[1]-u[0])/dy
    out[1:-1]=(u[2:]-u[:-2])/(2*dy)
    out[-1]=(u[-1]-u[-2])/dy
    return out
def sbp_identity(u,dy=1.):
    u=np.asarray(u,float)
    du=derivative(u,dy)
    weighted=dy*(u[0]*du[0]/2+np.dot(u[1:-1],du[1:-1])+u[-1]*du[-1]/2)
    rhs=(u[-1]*u[-1]-u[0]*u[0])/2
    assert math.isclose(weighted,rhs,rel_tol=1e-10,abs_tol=1e-9)
    return weighted,rhs
def physical_rhs(P,M,t,G,dy=1.):
    P=np.asarray(P,float);M=np.asarray(M,float)
    if P.ndim!=1 or M.shape!=P.shape or len(P)<3 or not 1<=t<=2 or dy<=0:
        raise ValueError('original t and matching normal grid')
    v=-1/math.sqrt(1+t*t);beta=(1+v)/(1-v)
    target=beta*P[0]-2*G/(1-v)
    pdot=(1+v)*derivative(P,dy)
    mdot=(v-1)*derivative(M,dy)
    pdot[-1]-=2*(1+v)/dy*P[-1]
    mdot[0]+=2*(1-v)/dy*(target-M[0])
    h=np.ones(len(P));h[0]=h[-1]=.5
    dE=2*dy*(np.dot(h*P,pdot)+np.dot(h*M,mdot))
    F=(1-v)*target**2-(1+v)*P[0]**2
    exact=F-(1+v)*P[-1]**2-(1-v)*M[-1]**2-(1-v)*(M[0]-target)**2
    assert math.isclose(dE,exact,rel_tol=1e-9,abs_tol=1e-8)
    assert dE<=2*math.sqrt(5)*G*G+1e-8
    return pdot,mdot,dict(energy_derivative=dE,exact_SBP_SAT_rhs=exact,
        Neumann_target=target,weak_boundary_residual=M[0]-target,
        original_SBP2_SAT_normal_semidiscrete_energy_closed=True,
        pointwise_strong_neumann_enforced=False,
        full_coupled_SSPRK3_stability_proved=False)
def audit():
    rng=np.random.default_rng(22);count=0
    for n in (8,16,32):
        for t in (1.,4/3,2.):
            P=rng.normal(size=n);M=rng.normal(size=n)
            physical_rhs(P,M,t,.2,.01);count+=1
    return dict(scheme='SBP2 diagonal H with weak SAT Neumann boundary',
      verified_original_neumann_samples=count,
      exact_normal_semidiscrete_source_energy_bound_closed=True,
      original_full_time_discrete_coupled_energy_proved=False,
      early_Weyl_receiver_converged=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
