#!/usr/bin/env python3
"""Original moving a=t AdS5 Neumann normal-only FULLY DISCRETE SSPRK3 energy.

Active P_j (j=0..N-2), P_far=0; M_j(j=1..N-1),
M_wall=beta*P_wall-2G/(1-v).
For h=dt/dy<=1/(1+1/sqrt(2)) in original t in [1,2],
forward Euler upwind normal transport is a convex neighbor average and
||FE state||²<=||state||²+h Fwall
                  <=||state||²+2sqrt(5)*h||G||².
SSPRK3 Jensen convexity yields forcing weights (1/6,2/3,1/6)
at times start, midpoint, end. No coupled radial/warp SSPRK3 or
pointwise Weyl receiver theorem is claimed.
"""
import json,math
import numpy as np
NORMAL_CFL_RATIO=1/(1+1/math.sqrt(2))
def energy(P,M):return float(np.sum(P*P)+np.sum(M*M))
def forward_euler(P,M,t,G,h):
    P=np.asarray(P,float);M=np.asarray(M,float);G=np.asarray(G,float)
    if P.ndim!=2 or P.shape!=M.shape or G.shape!=(P.shape[0],) or P.shape[1]<2:
        raise ValueError('matching channels and active normal grid')
    if not(1<=t<=2 and 0<=h<=NORMAL_CFL_RATIO):
        raise ValueError('original moving time or discrete Neumann normal CFL')
    v=-1/math.sqrt(1+t*t);beta=(1+v)/(1-v)
    alpha=(1+v)*h;gamma=(1-v)*h
    mwall=beta*P[:,0]-2*G/(1-v)
    Pnext=(1-alpha)*P+alpha*np.concatenate((P[:,1:],np.zeros((len(G),1))),axis=1)
    Mnext=(1-gamma)*M+gamma*np.concatenate((mwall[:,None],M[:,:-1]),axis=1)
    F=float(np.sum((1-v)*mwall*mwall-(1+v)*P[:,0]**2))
    gain=energy(Pnext,Mnext)-energy(P,M)
    assert gain<=h*F+1e-9*max(1,energy(P,M))
    assert F<=2*math.sqrt(5)*np.dot(G,G)+1e-9*max(1,energy(P,M))
    return Pnext,Mnext,dict(delta_energy=gain,wall_flux=F,
       original_FE_normal_neumann_energy_bound_verified=True)
def ssprk3(P,M,t0,tm,t1,G0,Gmid,G1,h):
    P=np.asarray(P,float);M=np.asarray(M,float)
    one,oneM,_=forward_euler(P,M,t0,G0,h)
    ep,em,_=forward_euler(one,oneM,t1,G1,h)
    two=.75*P+.25*ep;twoM=.75*M+.25*em
    ep,em,_=forward_euler(two,twoM,tm,Gmid,h)
    final=P/3+2*ep/3;finalM=M/3+2*em/3
    budget=h*2*math.sqrt(5)*(np.dot(G0,G0)/6+
        np.dot(G1,G1)/6+2*np.dot(Gmid,Gmid)/3)
    gain=energy(final,finalM)-energy(P,M)
    assert gain<=budget+1e-9*max(1,energy(P,M))
    return final,finalM,dict(ssprk3_normal_energy_gain=gain,
         forced_SSPRK3_energy_upper_bound=float(budget),
         original_normal_only_full_discrete_SSPRK3_contract=True,
         full_radial_warp_and_moving_bulk_energy_proved=False)
def audit():
    rng=np.random.default_rng(123);count=0
    for n in (8,16,32):
        for scale in (0.,.1,1.):
            P=rng.normal(size=(3,n));M=rng.normal(size=(3,n))
            g0=np.array([.2,-.1,.3])*scale
            gm=np.array([-.4,.2,.1])*scale
            g1=np.array([-.3,.1,-.2])*scale
            a,b,d=ssprk3(P,M,1.,1.5,2.,g0,gm,g1,.45)
            if scale==0:assert d['ssprk3_normal_energy_gain']<=1e-9
            count+=1
    return dict(original_uniform_normal_CFL=NORMAL_CFL_RATIO,
        forced_SSPRK3_stage_weights=['1/6','2/3','1/6'],
        validated_scenarios=count,
        fully_discrete_original_moving_neumann_normal_only_energy_closed=True,
        original_full_radial_warp_coupled_CFL_still_open=True,
        original_receiver_Weyl_convergence_still_open=True)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
