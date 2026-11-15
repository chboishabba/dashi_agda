#!/usr/bin/env python3
"""F8: ORIGINAL a=t Poincare AdS5 moving-wall retarded TT numerical controls.

The linear TT equations are solved on the actual z_b=1/t cosmological brane,
not on stationary RS2. For k along x, qplus=H_T+H_z, qminus=H_T-H_z;
characteristic upwind in y=z-b(T), SSPRK3 time, Fourier in x.
'plane': spatially compact x source, uniform transverse yy/zz directions:
  TOTAL energy infinite; per-transverse-area finite.
'compact_3d_TT': genuinely 3D compact radial bump acted on by local 4th
order TT differential projector, angular Fourier/Weyl inversion.
  Current UV/angular/grid controls FAIL acceptance; do not promote.
The output is numerical evidence, NOT a convergently certified solution,
not an empirical graviton, and does not close the complete B4 gate.

Sources: Caldwell-Langlois (2001), Hiramatsu-Koyama-Taruya (2003/04),
Ginoux-Murro (2022), Shiromizu-Maeda-Sasaki (2000).
"""
import json
import math
import sys
import time
import numpy as np
from numba import njit
from numpy.polynomial.legendre import leggauss
from scipy.special import spherical_jn

def F(t):
    return np.arcsinh(t)-np.sqrt(1+t*t)/t

@njit(cache=True)
def stage_rhs(U,P,M,K2,y,dy,v,b,amp,phihat,du,dp,dm):
    n,nk=U.shape
    for j in range(n):
        z=y[j]+b
        for k in range(nk):
            p=P[j,k]
            m=M[j,k]
            if j==0:
                m=(2*amp*phihat[k]-(1+v)*p)/(v-1)
            if j==n-1:
                p=0.0
            w=(p-m)*0.5
            force=-3*w/z-K2[k]*U[j,k]
            du[j,k]=0.5*((1+v)*p+(1-v)*m)
            if j==n-1:
                dp[j,k]=0.
            elif j<n-2:
                dp[j,k]=(v+1)*(-3*p+4*P[j+1,k]-P[j+2,k])/(2*dy)+force
            else:
                dp[j,k]=(v+1)*(P[j+1,k]-p)/dy+force
            if j==0:
                dm[j,k]=0.
            elif j>1:
                dm[j,k]=(v-1)*(3*m-4*M[j-1,k]+M[j-2,k])/(2*dy)+force
            else:
                dm[j,k]=(v-1)*(m-M[j-1,k])/dy+force

@njit(cache=True)
def enforce(P,M,v,amp,phihat):
    M[0,:]=(2*amp*phihat-(1+v)*P[0,:])/(v-1)
    P[-1,:]=0.

def calc(nX=512,dy=.007,dt=.0017,final_t=6.,eps=.024,pulse=.007,
         inside_chord=.008,drive_scale=1.,outer_y=2.8,source_type="plane"):
    if source_type not in ("plane","compact_3d_TT"):
        raise ValueError("unrecognized source type")
    if not (nX>=64 and nX%2==0 and 0<dy<.05 and 0<dt<dy/2 and
            2<final_t<=7 and 0<eps<.04 and 0<pulse<.03 and inside_chord>0):
        raise ValueError("solver parameters outside conservative tested range")
    L=4.
    x=np.arange(nX)*L/nX
    x=np.where(x<=L/2,x,x-L)
    phi=np.zeros(nX)
    mask=np.abs(x)<eps
    rr=x[mask]/eps
    phi[mask]=np.exp(-1/(1-rr*rr))
    phi/=phi.sum()*(L/nX)
    K2=(2*math.pi*np.fft.rfftfreq(nX,d=L/nX))**2
    k=np.sqrt(K2)
    if source_type=="plane":
        phihat=np.fft.rfft(phi).real
    else:
        nodes,weights=leggauss(96)
        rad=(nodes+1)/2
        weights=weights/2
        bump=np.exp(-1/(1-rad*rad))
        base=weights*rad*rad*bump
        phi_k=np.sum(base[:,None]*np.sinc(
            (rad[:,None]*eps*k[None,:])/math.pi),axis=0)/base.sum()
        phihat=eps**4*phi_k
    y=np.arange(int(outer_y/dy)+1)*dy
    U=np.zeros((len(y),len(K2)))
    P=U.copy(); M=U.copy()
    A=U.copy(); B=U.copy(); C=U.copy()
    U1=U.copy(); P1=U.copy(); M1=U.copy()
    U2=U.copy(); P2=U.copy(); M2=U.copy()
    tgrid=np.linspace(1,final_t+.05,12001)
    Tgrid=F(tgrid)
    T0,Tend=Tgrid[0],F(final_t)
    nt=int(np.ceil((Tend-T0)/dt))
    dt=(Tend-T0)/nt
    def coeff(T):
        t=float(np.interp(T,Tgrid,tgrid))
        v=-1/np.sqrt(1+t*t)
        b=1/t
        ds=T-T0
        q=2*ds/pulse-1
        shape=np.exp(1-1/(1-q*q)) if 0<ds<pulse else 0.
        amp=-6*drive_scale*np.sqrt(1-v*v)/b*shape
        return v,b,amp
    snap=[]
    for it in range(nt+2):
        T=T0+dt*it
        if it>=nt-1:
            snap.append(U[0,:].copy())
        if it==nt+1:
            break
        v,b,amp=coeff(T)
        enforce(P,M,v,amp,phihat)
        stage_rhs(U,P,M,K2,y,dy,v,b,amp,phihat,A,B,C)
        U1[:]=U+dt*A; P1[:]=P+dt*B; M1[:]=M+dt*C
        v,b,amp=coeff(T+dt)
        enforce(P1,M1,v,amp,phihat)
        stage_rhs(U1,P1,M1,K2,y,dy,v,b,amp,phihat,A,B,C)
        U2[:]=.75*U+.25*(U1+dt*A)
        P2[:]=.75*P+.25*(P1+dt*B)
        M2[:]=.75*M+.25*(M1+dt*C)
        v,b,amp=coeff(T+dt/2)
        enforce(P2,M2,v,amp,phihat)
        stage_rhs(U2,P2,M2,K2,y,dy,v,b,amp,phihat,A,B,C)
        U[:]=(U+2*(U2+dt*A))/3
        P[:]=(P+2*(P2+dt*B))/3
        M[:]=(M+2*(M2+dt*C))/3
    rx_front=float(np.sqrt((F(final_t)-F(1))**2-
                            (1-1/final_t)**2))
    rx=rx_front-inside_chord
    far_rx=rx_front+.15
    if source_type=="plane":
        def plane_eval(vals,r,deriv_xx=False):
            weight=np.ones(len(k))
            weight[1:-1]=2.
            if deriv_xx:
                weight=weight*(-K2)
            return float(np.sum(vals*weight*np.cos(k*r))/nX)
        ev=lambda vals:plane_eval(vals,rx)
        xev=lambda vals:plane_eval(vals,rx,True)
        far_field=plane_eval(snap[-2],far_rx)
    else:
        def angular(q,extra_xx=False):
            if not extra_xx:
                return 2*(2/5*spherical_jn(0,q)-
                          4/7*spherical_jn(2,q)+
                          1/35*spherical_jn(4,q))
            return 2*(22/105*spherical_jn(0,q)-
                      4/7*spherical_jn(2,q)+
                      81/385*spherical_jn(4,q)-
                      2/231*spherical_jn(6,q))
        dk=k[1]-k[0]
        def radial_eval(vals,r,deriv_xx=False):
            weight=dk/(4*math.pi**2)*k**6
            if deriv_xx:
                weight=weight*(-k*k)
            return float(np.dot(weight*angular(k*r,deriv_xx),vals))
        ev=lambda vals:radial_eval(vals,rx)
        xev=lambda vals:radial_eval(vals,rx,True)
        far_field=radial_eval(snap[-2],far_rx)
    H=ev(snap[-2])
    HT=ev((snap[-1]-snap[-3])/(2*dt))
    HTT=ev((snap[-1]-2*snap[-2]+snap[-3])/dt**2)
    Hxx=xev(snap[-2])
    t=final_t
    S=np.sqrt(1+t*t)/t
    # Intrinsic FOUR-dimensional FRW electric Weyl, not projected 5D Weyl.
    E=-(S*S*HTT-HT/(t*np.sqrt(1+t*t))+Hxx)/(4*t*t)
    margin=rx-eps-np.log(t)
    if margin<=0:
        raise ValueError("receiver is not photon-dark for entire source")
    if L-far_rx-eps-rx_front<=0:
        raise ValueError("periodic source image contaminates far control")
    if abs(drive_scale)<1e-12:
        assert H==0 and E==0 and far_field==0
    return dict(nX=nX,dy=dy,dt=dt,steps=nt,receiver_r=rx,
        spatial_support_halfwidth=eps,source_time_support=pulse,
        source_type=source_type,photon_dark=True,photon_margin=margin,
        retarded_tensor_Hyy=H,intrinsic_4D_electric_Weyl=E,
        HTT=HTT,Hxx=Hxx,observer_t=t,far_receiver_r=far_rx,
        far_field=far_field,
        far_to_receiver_ratio=abs(far_field)/max(abs(H),1e-30),
        source_amplitude=drive_scale,
        plane_symmetric_only=(source_type=="plane"),
        finite_total_3D_perturbation_energy=(source_type=="compact_3d_TT"),
        bulk_front_radius=rx_front,brane_photon_horizon=np.log(t),
        original_metric_a_equals_t=True,
        source_generated_by_matter_action=False,
        observed_graviton_signal=False,full_B4_gate_closed=False,
        verified_refinement_convergence=False)

if __name__=="__main__":
    tic=time.time()
    params=dict(nX=int(sys.argv[1]),dy=float(sys.argv[2]),
                dt=float(sys.argv[3]),
                source_type=sys.argv[4] if len(sys.argv)>4 else "plane") if len(sys.argv)>3 else {}
    print(json.dumps(calc(**params),indent=2))
    print("elapsed_s",time.time()-tic)
