#!/usr/bin/env python3
"""Original KSW moving Neumann normal SBP and legacy boundary counterexample.

With P_far=0, M_wall=beta P_wall-2G/(1-v), first-order upwind
characteristic derivatives obey EXACT finite-grid energy telescoping:
2dy*Q = F_wall -(1+v)*sum(diff(P)^2)
                 -(1-v)*sum(diff(M)^2)-(1-v)*M_far^2.
F_wall <=2sqrt(5)*G^2 on original t in [1,2].
Legacy 2nd-order outgoing derivative with first-order boundary closure
has a 16-node integer homogeneous P witness P·D_+ P=277/2>0.
These statements prove normal-only UNWEIGHTED transport dissipation;
full moving weighted bulk/SSPRK3/receiver acceptance remains OPEN.
"""
import json,math
from fractions import Fraction
import numpy as np
LEGACY_WITNESS=np.array([0,0,-1,-2,-2,-1,1,4,10,19,30,41,51,53,40,0],float)
def derivative_plus(p,order=1,dy=1.):
    p=np.asarray(p,float)
    if len(p)<4 or dy<=0 or p[-1]!=0:raise ValueError('P_far=0, finite grid')
    result=np.zeros_like(p)
    for j in range(len(p)-1):
        if order==1 or j==len(p)-2:result[j]=(p[j+1]-p[j])/dy
        elif order==2:result[j]=(-3*p[j]+4*p[j+1]-p[j+2])/(2*dy)
        else:raise ValueError('supported normal order 1 or 2')
    return result
def derivative_minus(m,order=1,dy=1.):
    m=np.asarray(m,float)
    if len(m)<4 or dy<=0:raise ValueError('M finite grid')
    result=np.zeros_like(m)
    for j in range(1,len(m)):
        if order==1 or j==1:result[j]=(m[j]-m[j-1])/dy
        elif order==2:result[j]=(3*m[j]-4*m[j-1]+m[j-2])/(2*dy)
        else:raise ValueError('supported normal order 1 or 2')
    return result
def evaluate(t,p,m,G=0.,dy=1.,order=1):
    if not 1<=t<=2:raise ValueError('original a=t t in [1,2]')
    v=-1/math.sqrt(1+t*t);beta=(1+v)/(1-v)
    p=np.asarray(p,float).copy();m=np.asarray(m,float).copy()
    if p.shape!=m.shape or p[-1]!=0:raise ValueError('matching grid and P_far=0')
    m[0]=beta*p[0]-2*G/(1-v)
    Q=(1+v)*float(np.dot(p,derivative_plus(p,order,dy)))
    Q+=(v-1)*float(np.dot(m,derivative_minus(m,order,dy)))
    F=(1-v)*m[0]**2-(1+v)*p[0]**2
    exact=(F-(1+v)*sum(np.diff(p)**2)
       -(1-v)*sum(np.diff(m)**2)-(1-v)*m[-1]**2)/(2*dy)
    return dict(order=order,energy_production_Q=Q,SBP_rhs=exact,
       exact_SBP_holds=(abs(Q-exact)<1e-9) if order==1 else None,
       original_wall_flux=F,original_source_uniform_wall_bound=2*math.sqrt(5)*G*G,
       full_moving_weighted_discrete_energy_accepted=False)
def legacy_counterexample():
    v=LEGACY_WITNESS
    iv=list(map(int,v));q=Fraction(0)
    for j in range(len(iv)-1):
        deriv=(Fraction(-3*iv[j]+4*iv[j+1]-iv[j+2],2)
               if j<len(iv)-2 else Fraction(iv[j+1]-iv[j]))
        q+=iv[j]*deriv
    assert q==Fraction(277,2)
    old=evaluate(1.5,v,np.zeros_like(v),order=2)
    new=evaluate(1.5,v,np.zeros_like(v),order=1)
    assert old['energy_production_Q']>0 and new['energy_production_Q']<0
    return dict(integer_vector=iv,exact_legacy_outgoing_energy='277/2',
       old_homogeneous_energy_production=old['energy_production_Q'],
       new_SBP_homogeneous_energy_production=new['energy_production_Q'],
       legacy_boundary_closure_is_dissipative=False)
def audit():
    rng=np.random.default_rng(5);count=0
    for n in (8,16,32):
        for t in (1.,4/3,2.):
            p=rng.normal(size=n);p[-1]=0;m=rng.normal(size=n)
            d=evaluate(t,p,m,.2,.02,1)
            assert d['exact_SBP_holds']
            assert 2*.02*d['energy_production_Q']<=d['original_source_uniform_wall_bound']+1e-9
            count+=1
    return dict(counterexample=legacy_counterexample(),SBP_samples=count,
       original_moving_1st_order_normal_transport_SBP_closed=True,
       original_moving_full_discrete_SSPRK3_energy_closed=False,
       actual_early_Weyl_receiver_converged=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
