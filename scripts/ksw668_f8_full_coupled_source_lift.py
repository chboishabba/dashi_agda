#!/usr/bin/env python3
"""Original a=t AdS5 *coupled* nonhomogeneous semidiscrete energy via a
characteristic algebraic source lift (NOT a scalar metric/matter action):
Lambda_U=Lambda_P=0; Lambda_M=-2G(T,r)chi(y)/(1-v(T)), chi(0)=1.
The lifted original weak SAT wall is homogeneous. The bulk residual
F=(c Lambda_M, 3 Lambda_M/(2z),
   (v-1)Dw Lambda_M+3 Lambda_M/(2z)-dT Lambda_M).
The exact coupled homogeneous estimate yields
Etilde'<=6 Etilde +0.5||F||_E², including radial gradient of F_U.
No fully discrete SSPRK3 or pointwise Weyl transfer is implied.
"""
import json
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import (
    coeff,weighted_normal_D,radial_stiffness,setup,full_energy_derivative)

def chi_compact(y,y_cut):
    if y_cut<=0:raise ValueError('positive compact normal cutoff')
    u=y/y_cut;out=np.zeros_like(u)
    mask=u<1
    out[mask]=np.exp(1-1/(1-u[mask]**2))
    assert abs(out[0]-1)<1e-13
    return out

def source_lift(data,G,GT,cutoff=.12):
    U,P,M=[data[x] for x in ('U','P','M')]
    _,ny,nr=U.shape
    G=np.asarray(G,float);GT=np.asarray(GT,float)
    if G.shape!=(3,nr) or GT.shape!=G.shape:raise ValueError('original TT modal source shape')
    b,v,vdot,a,c=coeff(data['t'])
    y=np.arange(ny)*data['dy'];chi=chi_compact(y,cutoff)
    Lam=-2*chi[None,:,None]*G[:,None,:]/(1-v)
    LamT=-2*chi[None,:,None]*(GT[:,None,:]/(1-v)+G[:,None,:]*vdot/(1-v)**2)
    F_U=c*Lam
    F_P=3*Lam/(2*data['z'][None,:,None])
    F_M=np.empty_like(Lam)
    for q in range(3):
        for j in range(nr):
            F_M[q,:,j]=((v-1)*weighted_normal_D(Lam[q,:,j],data['z'],data['dy'])
                  +3*Lam[q,:,j]/(2*data['z'])-LamT[q,:,j])
    target=-2*G/(1-v)
    assert np.allclose(Lam[:,0,:],target,rtol=1e-12,atol=1e-12)
    return dict(lift_M=Lam,lift_M_T=LamT,
       F_U=F_U,F_P=F_P,F_M=F_M,
       wall_target=target,
       weak_original_Israel_boundary_homogenized=True)

def check(data,G,GT,cutoff=.12):
    L=source_lift(data,G,GT,cutoff)
    full={k:(v.copy() if isinstance(v,np.ndarray) else v) for k,v in data.items()}
    full['M']=data['M']+L['lift_M']
    original=full_energy_derivative(full,source=G,return_derivatives=True)
    homogeneous=full_energy_derivative(data,return_derivatives=True)
    diff={
       'U':original['Udot']-homogeneous['Udot'],
       'P':original['Pdot']-homogeneous['Pdot'],
       'M':original['Mdot']-homogeneous['Mdot']-L['lift_M_T']}
    residual=max(float(np.max(np.abs(diff[k]-L['F_'+k]))) for k in ('U','P','M'))
    assert residual<1e-9,residual
    b,v,vdot,a,c=coeff(data['t'])
    V=[];radialF=[]
    for q,d in enumerate((3,7,11)):
        LR,vr=radial_stiffness(d,data['U'].shape[-1],data['dr'])
        V.append(vr);radialF.append(L['F_U'][q]@LR.T)
    V=np.array(V);rF=np.array(radialF)
    weight=data['H'][None,:,None]*data['w'][None,:,None]*V[:,None,:]
    FU,FP,FM=[L['F_'+k] for k in ('U','P','M')]
    Fnorm2=float(np.sum(weight*(a*FP**2+c*FM**2-FU*rF)))
    assert Fnorm2>=-1e-9
    work=float(np.sum(weight*(a*data['P']*FP+c*data['M']*FM-data['U']*rF)))
    Eprime=homogeneous['Eprime']+work
    bound=6*homogeneous['E']+.5*Fnorm2
    assert Eprime<=bound+1e-8*max(1,bound)
    return dict(t=data['t'],exact_lift_residual=residual,
       E=homogeneous['E'],Eprime_with_volume_force=Eprime,
       source_weighted_norm_sq=Fnorm2,
       Eprime_upper_6E_half_Fnorm=bound,
       original_coupled_forced_semidiscrete_energy_closed=True,
       physical_scalar_metric_lift_proved=False,
       full_coupled_SSPRK3_time_discrete_closed=False,
       original_both_pointwise_Weyl_trace_closed=False)

def audit():
    rows=[]
    for t,seed,ny,nr,dy,dr in ((1.,1,9,5,.015,.03),(4/3,2,11,7,.013,.025),(2.,3,17,9,.01,.02)):
        data=setup(ny,nr,dy,dr,t,seed)
        rng=np.random.default_rng(seed+55)
        G=rng.normal(size=(3,nr))*.03
        GT=rng.normal(size=(3,nr))*.02
        rows.append(check(data,G,GT,cutoff=dy*5))
    return dict(cases=rows,
       full_original_T_y_r_forced_semidiscrete_energy_closed=True,
       explicit_original_moving_weak_Israel_characteristic_source_lift=True,
       entire_coupled_RK3_and_Weyl_receiver_convergence_open=True)

if __name__=='__main__':print(json.dumps(audit(),indent=2))
