#!/usr/bin/env python3
"""Original moving AdS5 compact TT yy: exact angular multipoles l=0,2,4.
For f(radial), axisymmetric m=0 part of local TT_yy has Legendre
coefficients f_l(r); l=0,2,4. Writing H_l=(r/eps)^l V_l,
each V_l solves the wave equation with effective radial dimension 3+2*l
and original moving Neumann Israel source f_l/(r/eps)^l.
No spatial FFT / post-evolution four spatial derivatives. Grid refinement
and full Weyl readout remain separate open acceptance requirements.
"""
import json, math, functools
import numpy as np
import sympy as sp
from numba import njit
from ksw668_f8_fv_source_flux import exact_cell_averages,total_scaled_moments

@functools.lru_cache(maxsize=1)
def profiles():
    u=sp.symbols('u', positive=True)
    f=sp.exp(1-1/(1-u*u))
    dd=[None]+[sp.diff(f,u,i) for i in range(1,5)]
    forms={
       0:sp.Rational(2,5)*(dd[4]+4*dd[3]/u),
       2:sp.Rational(4,7)*(dd[4]+dd[3]/u-6*dd[2]/u**2+6*dd[1]/u**3),
       4:sp.Rational(1,35)*(dd[4]-6*dd[3]/u+15*dd[2]/u**2-15*dd[1]/u**3)}
    return [(ell,sp.lambdify(u,sp.factor(form/u**ell),'numpy'),
             float(sp.limit(form/u**ell,u,0))) for ell,form in forms.items()]

def normalized_sources(eps,rgrid):
    if eps<=0:raise ValueError('positive support')
    u=np.asarray(rgrid)/eps
    a=np.zeros((3,len(u)))
    mask=(u>0)&(u<1)
    for t,(ell,fun,origin) in enumerate(profiles()):
        a[t,0]=origin
        if np.any(mask):a[t,mask]=fun(u[mask])
    assert np.all(a[:,u>=1]==0)
    assert np.isfinite(a).all()
    return a

def averaged_sources(eps,rgrid,dr,quad_nodes=48):
    """Weighted radial-cell average of exact compact TT multipole source.

    Integrate the analytic smooth source using the true effective
    d=3+2*ell radial volume measure. Cells crossing source edge
    may extend up to dr/2 beyond eps; the photon-dark gate accounts
    for this discrete-support enlargement.
    """
    if quad_nodes<8:raise ValueError('source quadrature too small')
    x,w=np.polynomial.legendre.leggauss(quad_nodes)
    a=np.zeros((3,len(rgrid)))
    for j,r in enumerate(rgrid):
        lo=max(0.,r-dr/2);hi=min(eps,r+dr/2)
        if hi<=lo:continue
        radii=lo+(hi-lo)*(x+1)/2
        u=radii/eps
        for q,(ell,fun,origin) in enumerate(profiles()):
            dimension=3+2*ell
            integrand=w*(radii**(dimension-1))*fun(u)
            moment=float(np.sum(integrand)*(hi-lo)/2)
            cell_full_upper=r+dr/2
            denominator=(cell_full_upper**dimension-lo**dimension)/dimension
            a[q,j]=moment/denominator
    return a

@njit(cache=True)
def stage(U,P,M,outU,outP,outM,dr,dy,b,v,amplitude,sources,cp,cm,normal_order=2):
    nm,ny,nr=U.shape
    d2=dr*dr
    for q in range(nm):
        d=3+4*q
        for iy in range(ny):
            z=b+iy*dy
            for ir in range(nr):
                p=P[q,iy,ir] if iy<ny-1 or normal_order==3 else 0.
                m=M[q,iy,ir]
                if iy==0 and normal_order!=3:
                    m=(2*amplitude*sources[q,ir]-(1+v)*p)/(v-1)
                w=.5*(p-m)
                if ir==nr-1:
                    outU[q,iy,ir]=0.;outP[q,iy,ir]=0.;outM[q,iy,ir]=0.
                    continue
                if ir==0:
                    radial=2*d*(U[q,iy,1]-U[q,iy,0])/d2
                else:
                    coeffplus=cp[q,ir]
                    coeffminus=cm[q,ir]
                    radial=(coeffplus*(U[q,iy,ir+1]-U[q,iy,ir])-
                        coeffminus*(U[q,iy,ir]-U[q,iy,ir-1]))/d2
                force=radial-3*w/z
                outU[q,iy,ir]=.5*((1+v)*p+(1-v)*m)
                if normal_order==3:
                    dpy=(P[q,iy+1,ir]-p)/dy if iy==0 else ((p-P[q,iy-1,ir])/dy if iy==ny-1 else (P[q,iy+1,ir]-P[q,iy-1,ir])/(2*dy))
                    outP[q,iy,ir]=(1+v)*dpy+force
                    if iy==ny-1:outP[q,iy,ir]-=2*(1+v)*p/dy
                elif iy==ny-1:
                    outP[q,iy,ir]=0.
                elif normal_order==1:
                    outP[q,iy,ir]=(1+v)*(P[q,iy+1,ir]-p)/dy+force
                elif iy<ny-2:
                    outP[q,iy,ir]=(1+v)*(-3*p+4*P[q,iy+1,ir]-P[q,iy+2,ir])/(2*dy)+force
                else:
                    outP[q,iy,ir]=(1+v)*(P[q,iy+1,ir]-p)/dy+force
                if normal_order==3:
                    dmy=(M[q,iy+1,ir]-m)/dy if iy==0 else ((m-M[q,iy-1,ir])/dy if iy==ny-1 else (M[q,iy+1,ir]-M[q,iy-1,ir])/(2*dy))
                    outM[q,iy,ir]=(v-1)*dmy+force
                    if iy==0:
                        target=(2*amplitude*sources[q,ir]-(1+v)*p)/(v-1)
                        outM[q,iy,ir]+=2*(1-v)*(target-m)/dy
                elif iy==0:
                    outM[q,iy,ir]=0.
                elif normal_order==1:
                    outM[q,iy,ir]=(v-1)*(m-M[q,iy-1,ir])/dy+force
                elif iy>1:
                    outM[q,iy,ir]=(v-1)*(3*m-4*M[q,iy-1,ir]+M[q,iy-2,ir])/(2*dy)+force
                else:
                    outM[q,iy,ir]=(v-1)*(m-M[q,iy-1,ir])/dy+force

@njit(cache=True)
def enforce(U,P,M,v,amp,sources,normal_order=2):
    if normal_order!=3:
        M[:,0,:]=(2*amp*sources-(1+v)*P[:,0,:])/(v-1)
        P[:,-1,:]=0
    U[:,:,-1]=0;P[:,:,-1]=0;M[:,:,-1]=0

def F(t):return math.asinh(t)-math.sqrt(1+t*t)/t

def propagate(dr=.008,dy=.012,dt=.0015,eps=.04,final_t=12,
              pulse=.065,inside_chord=.012,r_outer=4.3,y_outer=3.0,drive=1.,
              conservative_source=True,normal_order=2,checkpoint=None,budget=75.,checkpoint_every=8):
    if normal_order not in (1,2,3):raise ValueError('normal order must be 1 SBP, 2 legacy, 3 SBP2 SAT')
    if not(2<final_t<=20 and 0<dr<eps/3 and 0<dy<=.03
            and 0<dt<min(dr*math.sqrt(3/44),dy*.45) and 0<eps<.08
            and r_outer>3 and y_outer>2 and 0<pulse<.12):
        raise ValueError('positive original-model parameters / resolved source')
    T0,Tend=F(1),F(final_t)
    span=Tend-T0
    bulk=math.sqrt(span*span-(1-1/final_t)**2)
    rx=bulk-inside_chord
    gap=rx-eps-math.log(final_t)
    if gap<=dr/2:raise ValueError('receiver inside numerical source half-cell photon cone')
    nr=int(math.ceil(r_outer/dr))+1
    ny=int(math.ceil(y_outer/dy))+1
    rg=np.arange(nr)*dr
    # Exact moment-primitive cell integration for local compact TT source.
    src=(exact_cell_averages(eps,rg,dr) if conservative_source
         else normalized_sources(eps,rg))
    source_conservative_moments=None
    if conservative_source:
        source_conservative_moments=[]
        for q,ell in enumerate((0,2,4)):
            d=3+2*ell
            volumes=((rg+dr/2)**d-np.maximum(rg-dr/2,0)**d)/d
            source_conservative_moments.append(float(np.dot(volumes,src[q])/eps**d))
        targets=total_scaled_moments()
        if (abs(source_conservative_moments[0])>1e-7
           or abs(source_conservative_moments[1])>1e-7
           or abs(source_conservative_moments[2]-targets['l4'])>1e-7):
            raise ValueError('Original compact TT source cell moments fail conservative exact integration')
    cp=np.zeros((3,nr));cm=np.zeros((3,nr))
    for q in range(3):
        ell=2*q
        for j in range(1,nr):
            # Correct shell-volume conservative FV. Old centre-volume
            # approximation violates Delta_d(r²)=2d, especially for d=11.
            d=3+2*ell
            den=(j+.5)**d-(j-.5)**d
            cp[q,j]=d*(j+.5)**(d-1)/den
            cm[q,j]=d*(j-.5)**(d-1)/den
    initial_source_support=np.where(np.any(src!=0,axis=0))[0]
    assert len(initial_source_support)>3
    nt=int(math.ceil(span/dt));dt=span/nt
    dims=(3,ny,nr)
    U=np.zeros(dims);P=U.copy();M=U.copy()
    dU=U.copy();dP=U.copy();dM=U.copy()
    U1=U.copy();P1=U.copy();M1=U.copy()
    U2=U.copy();P2=U.copy();M2=U.copy()
    def coeff(T):
        t=max(1.,math.exp(T+1)/2)
        for _ in range(7):
            t-=(F(t)-T)/(math.sqrt(1+t*t)/t**2)
            if t<.5:t=.5
        v=-1/math.sqrt(1+t*t)
        b=1/t
        ds=T-T0
        q=2*ds/pulse-1
        amp=(-6*drive*math.sqrt(1-v*v)/b*
             math.exp(1-1/(1-q*q)) if 0<ds<pulse else 0.)
        return v,b,amp
    prev_wall=None
    now_wall=None
    prev_walldot=None
    now_walldot=None
    start_it=0
    if checkpoint is not None:
        from ksw668_f8_ssprk_checkpoint import NativeCheckpoint
        ck=NativeCheckpoint(checkpoint,dict(dr=dr,dy=dy,dt=dt,eps=eps,final_t=final_t,
            pulse=pulse,inside_chord=inside_chord,r_outer=r_outer,y_outer=y_outer,drive=drive,
            conservative_source=conservative_source,normal_order=normal_order,nt=nt),
            dims,src,cp,cm)
        saved=ck.load()
        if saved is not None:
            start_it,U,P,M,prev_wall,now_wall,prev_walldot,now_walldot=saved
        ck.start()
    for it in range(start_it,nt+1):
        if it==nt-1:prev_wall=U[:,0,:].copy()
        if it==nt:now_wall=U[:,0,:].copy()
        T=T0+it*dt
        v,b,amp=coeff(T)
        enforce(U,P,M,v,amp,src,normal_order)
        stage(U,P,M,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm,normal_order)
        if it==nt-1:prev_walldot=dU[:,0,:].copy()
        if it==nt:now_walldot=dU[:,0,:].copy()
        U1[:]=U+dt*dU;P1[:]=P+dt*dP;M1[:]=M+dt*dM
        v,b,amp=coeff(T+dt)
        enforce(U1,P1,M1,v,amp,src,normal_order)
        stage(U1,P1,M1,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm,normal_order)
        U2[:]=.75*U+.25*(U1+dt*dU)
        P2[:]=.75*P+.25*(P1+dt*dP)
        M2[:]=.75*M+.25*(M1+dt*dM)
        v,b,amp=coeff(T+dt/2)
        enforce(U2,P2,M2,v,amp,src,normal_order)
        stage(U2,P2,M2,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm,normal_order)
        U[:]=(U+2*(U2+dt*dU))/3
        P[:]=(P+2*(P2+dt*dP))/3
        M[:]=(M+2*(M2+dt*dM))/3
        if checkpoint is not None:
            cursor=it+1
            if cursor%checkpoint_every==0 or cursor==nt+1 or ck.expired(budget):
                ck.save(cursor,U,P,M,prev_wall,now_wall,prev_walldot,now_walldot)
                if cursor<nt+1 and ck.expired(budget):
                    raise InterruptedError(f'checkpoint saved at step {cursor}/{nt+1}')
    next_wall=U[:,0,:].copy()
    v,b,amp=coeff(T0+(nt+1)*dt)
    enforce(U,P,M,v,amp,src,normal_order)
    stage(U,P,M,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm,normal_order)
    next_walldot=dU[:,0,:].copy()
    def read_all(r):
        x=r/dr;ir=int(math.floor(x));q=x-ir
        if ir<1 or ir+2>=nr:raise ValueError('receiver interior to grid')
        weights=np.array([-q*(q-1)*(q-2)/6,
                           (q+1)*(q-1)*(q-2)/2,
                          -(q+1)*q*(q-2)/2,
                           (q+1)*q*(q-1)/6])
        dw=np.array([-(3*q*q-6*q+2)/6,
                     (3*q*q-4*q-1)/2,
                     (-3*q*q+2*q+2)/2,
                     (3*q*q-1)/6])/dr
        d2w=np.array([1-q,3*q-2,1-3*q,q])/dr**2
        pieces=[];derivxx=[];lapieces=[]
        tprev=[];tnext=[];tdot=[];tdotprev=[];tdotnext=[]
        for j in range(3):
            ell=2*j;factor=(r/eps)**ell
            vj=now_wall[j,ir-1:ir+3]
            val=float(np.dot(weights,vj))
            v1=float(np.dot(dw,vj));v2=float(np.dot(d2w,vj))
            pieces.append(factor*val)
            derivxx.append(factor*(v2+2*ell*v1/r+ell*(ell-1)*val/r**2))
            lapieces.append(factor*(v2+(2*ell+2)*v1/r))
            tprev.append(factor*float(np.dot(weights,prev_wall[j,ir-1:ir+3])))
            tnext.append(factor*float(np.dot(weights,next_wall[j,ir-1:ir+3])))
            tdot.append(factor*float(np.dot(weights,now_walldot[j,ir-1:ir+3])))
            tdotprev.append(factor*float(np.dot(weights,prev_walldot[j,ir-1:ir+3])))
            tdotnext.append(factor*float(np.dot(weights,next_walldot[j,ir-1:ir+3])))
        H=sum(pieces)
        HT=(sum(tnext)-sum(tprev))/(2*dt)
        HTT=(sum(tnext)-2*H+sum(tprev))/(dt*dt)
        HT_from_tangent=sum(tdot)
        HTT_from_tangent=(sum(tdotnext)-sum(tdotprev))/(2*dt)
        S=math.sqrt(1+final_t*final_t)/final_t
        Heta=S*HT
        Hetaeta=S*S*HTT-HT/(final_t*math.sqrt(1+final_t*final_t))
        Hetaeta_tangent=S*S*HTT_from_tangent-HT_from_tangent/(final_t*math.sqrt(1+final_t*final_t))
        E4_legacy=-(Hetaeta+sum(derivxx))/(4*final_t**2)
        E4=-(Hetaeta+sum(lapieces))/(4*final_t**2)
        E4_tangent_legacy=-(Hetaeta_tangent+sum(derivxx))/(4*final_t**2)
        E4_tangent=-(Hetaeta_tangent+sum(lapieces))/(4*final_t**2)
        # Source-free receiver: SMS projected 5D Weyl=-delta G4 TT.
        E5=-(Hetaeta+2*Heta-sum(lapieces))/(2*final_t**2)
        E5_tangent=-(Hetaeta_tangent+2*S*HT_from_tangent-sum(lapieces))/(2*final_t**2)
        mode_HT=[(tnext[j]-tprev[j])/(2*dt) for j in range(3)]
        mode_HTT=[(tnext[j]-2*pieces[j]+tprev[j])/(dt*dt) for j in range(3)]
        mode_Heta=[S*x for x in mode_HT]
        mode_Hetaeta=[S*S*mode_HTT[j]-mode_HT[j]/(final_t*math.sqrt(1+final_t*final_t)) for j in range(3)]
        mode_E4_legacy=[-(mode_Hetaeta[j]+derivxx[j])/(4*final_t**2) for j in range(3)]
        mode_E4=[-(mode_Hetaeta[j]+lapieces[j])/(4*final_t**2) for j in range(3)]
        mode_E5=[-(mode_Hetaeta[j]+2*mode_Heta[j]-lapieces[j])/(2*final_t**2) for j in range(3)]
        # Two independently discretized temporal readouts, per physical q.
        # These are diagnostics, NOT upper bounds on continuum Weyl error.
        mode_HT_tangent=list(tdot)
        mode_HTT_tangent=[(tdotnext[j]-tdotprev[j])/(2*dt) for j in range(3)]
        Seta=-1/(final_t*math.sqrt(1+final_t*final_t))
        mode_Hetaeta_tangent=[S*S*mode_HTT_tangent[j]+Seta*mode_HT_tangent[j] for j in range(3)]
        mode_E4_tangent_legacy=[-(mode_Hetaeta_tangent[j]+derivxx[j])/(4*final_t**2) for j in range(3)]
        mode_E4_tangent=[-(mode_Hetaeta_tangent[j]+lapieces[j])/(4*final_t**2) for j in range(3)]
        mode_E5_tangent=[-(mode_Hetaeta_tangent[j]+2*S*mode_HT_tangent[j]-lapieces[j])/(2*final_t**2) for j in range(3)]
        if (abs(sum(mode_E4_tangent)-E4_tangent)>1e-10*max(1.,abs(E4_tangent))
            or abs(sum(mode_E5_tangent)-E5_tangent)>1e-10*max(1.,abs(E5_tangent))):
            raise ValueError('Original per-channel stage-derivative Weyl sum inconsistent')
        mode_delta_HT=[mode_HT[j]-mode_HT_tangent[j] for j in range(3)]
        mode_delta_HTT=[mode_HTT[j]-mode_HTT_tangent[j] for j in range(3)]
        for j in range(3):
            assert abs((mode_E4[j]-mode_E4_tangent[j])
                -(-S*S*mode_delta_HTT[j]-Seta*mode_delta_HT[j])/(4*final_t**2))<1e-10
            assert abs((mode_E5[j]-mode_E5_tangent[j])
                -(-S*S*mode_delta_HTT[j]-(Seta+2*S)*mode_delta_HT[j])/(2*final_t**2))<1e-10
        for mode_values,total in ((pieces,H),(mode_E4,E4),(mode_E5,E5)):
            if abs(sum(mode_values)-total)>1e-10*max(1.,abs(total)):
                raise ValueError('Original ternary-channel linear Weyl reconstruction inconsistent')
        return dict(mode_ternary_digits=[0,1,2],mode_ell=[0,2,4],
           mode_E4=mode_E4,mode_E5=mode_E5,
           mode_E4_tangent=mode_E4_tangent,mode_E5_tangent=mode_E5_tangent,
           mode_E4_legacy=mode_E4_legacy,mode_E4_tangent_legacy=mode_E4_tangent_legacy,
           mode_HT=mode_HT,mode_HT_tangent=mode_HT_tangent,
           mode_HTT=mode_HTT,mode_HTT_tangent=mode_HTT_tangent,
           mode_delta_HT=mode_delta_HT,mode_delta_HTT=mode_delta_HTT,
           mode_Hxx=derivxx,mode_Delta3H=lapieces,
           E4_tangent=E4_tangent,E5_tangent=E5_tangent,
           E4_legacy=E4_legacy,E4_tangent_legacy=E4_tangent_legacy,
           HT_from_tangent=HT_from_tangent,HTT_from_tangent=HTT_from_tangent,
           r=r,mode_values=pieces,H=H,Hxx=sum(derivxx),
           Delta3H=sum(lapieces),HT=HT,HTT=HTT,
           intrinsic4D_Eyy=E4,projected5D_Eyy=E5)
    rec=read_all(rx)
    far=read_all(bulk+.1)
    rr,components,yy=rec['r'],rec['mode_values'],rec['H']
    far_r,fc,fy=far['r'],far['mode_values'],far['H']
    return dict(model='original moving AdS5 a=t Neumann compact TT',
        original_radial_multipoles=[0,2,4],
        normal_order=normal_order,
        normal_only_characteristic_SBP_closed=(normal_order==1),
        normal_second_order_SBP_SAT_weak_neumann=(normal_order==3),
        strong_wall_neumann_enforced=(normal_order!=3),
        full_coupled_weighted_SSPRK3_energy_proved=False,
        effective_radial_dimensions=[3,7,11],
        step_radial=dr,step_bulk=dy,step_time=dt,
        radius_bins=nr,bulk_bins=ny,steps=nt,
        eps=eps,pulse=pulse,receiver_t=final_t,
        nominal_receiver_r=rx,receiver_grid_r=rr,
        source_adjusted_brane_photon_margin=gap,
        discrete_support_photon_margin=gap-dr/2,
        conservative_source_cell_average=conservative_source,
        source_cell_integration='exact compact TT endpoint primitives' if conservative_source else 'point sampling',
        normalized_conservative_cell_moments=source_conservative_moments,
        corrected_radial_shell_volume=True,
        radial_polynomial_r2_consistency_exact=True,
        radial_discrete_green_energy_nonpositive=True,
        source_weighted_moments_l0_l2_zero=True,
        radial_only_SSPRK3_Gershgorin_CFL_guard=math.sqrt(3/44),
        full_moving_T_y_r_SSPRK3_stability_certified=False,
        receiver_convergence_not_implied_by_discrete_energy=True,
        raw_mode_values=components,
        unsigned_ternary_mode_digits=[0,1,2],
        unsigned_ternary_harmonic_ell=[0,2,4],
        unsigned_ternary_codec_not_physical_C3_action=True,
        receiver_mode_intrinsic_4D_electric_Weyl=rec['mode_E4'],
        receiver_mode_projected_5D_electric_Weyl=rec['mode_E5'],
        receiver_mode_intrinsic_4D_electric_Weyl_tangent=rec['mode_E4_tangent'],
        receiver_mode_projected_5D_electric_Weyl_tangent=rec['mode_E5_tangent'],
        receiver_mode_H_T_derivative_readout_disagreement=rec['mode_delta_HT'],
        receiver_mode_H_TT_derivative_readout_disagreement=rec['mode_delta_HTT'],
        far_mode_intrinsic_4D_electric_Weyl=far['mode_E4'],
        far_mode_projected_5D_electric_Weyl=far['mode_E5'],
        far_mode_intrinsic_4D_electric_Weyl_tangent=far['mode_E4_tangent'],
        far_mode_projected_5D_electric_Weyl_tangent=far['mode_E5_tangent'],
        receiver_mode_Hxx=rec['mode_Hxx'],
        receiver_mode_Delta3H=rec['mode_Delta3H'],
        receiver_mode_intrinsic_4D_electric_Weyl_legacy_axial=rec['mode_E4_legacy'],
        receiver_mode_intrinsic_4D_electric_Weyl_tangent_legacy_axial=rec['mode_E4_tangent_legacy'],
        far_mode_intrinsic_4D_electric_Weyl_legacy_axial=far['mode_E4_legacy'],
        far_mode_intrinsic_4D_electric_Weyl_tangent_legacy_axial=far['mode_E4_tangent_legacy'],
        intrinsic_4D_weyl_spatial_operator='full_reconstructed_Delta3',
        receiver_dual_Weyl_temporal_second_derivative_cancellation=rec['projected5D_Eyy']-2*rec['intrinsic4D_Eyy'],
        retarded_TT_yy_scaled_by_eps4=yy,
        far_receiver_grid_r=far_r,far_mode_values=fc,
        far_TT_yy_scaled_by_eps4=fy,
        fixed_physical_receiver_cubic_interpolation=True,
        receiver_intrinsic_4D_electric_Weyl=rec['intrinsic4D_Eyy'],
        receiver_projected_5D_electric_Weyl=rec['projected5D_Eyy'],
        far_intrinsic_4D_electric_Weyl=far['intrinsic4D_Eyy'],
        far_projected_5D_electric_Weyl=far['projected5D_Eyy'],
        receiver_intrinsic_4D_electric_Weyl_tangent=rec['E4_tangent'],
         receiver_intrinsic_4D_electric_Weyl_legacy_axial=rec['E4_legacy'],
         receiver_intrinsic_4D_electric_Weyl_tangent_legacy_axial=rec['E4_tangent_legacy'],
        receiver_projected_5D_electric_Weyl_tangent=rec['E5_tangent'],
        far_intrinsic_4D_electric_Weyl_tangent=far['E4_tangent'],
         far_intrinsic_4D_electric_Weyl_legacy_axial=far['E4_legacy'],
         far_intrinsic_4D_electric_Weyl_tangent_legacy_axial=far['E4_tangent_legacy'],
        far_projected_5D_electric_Weyl_tangent=far['E5_tangent'],
        second_order_spatial_radial_readout=True,
        no_post_evolution_spatial_derivatives=False,
        no_spatial_Fourier_Bessel_inverse=True,
        compact_support_of_boundary_stress=True,
        numerical_convergence_certified=False,
        both_Weyl_numerically_evaluated=True,
        full_Weyl_receiver_certified=False,
        Agda_kernel_accepted=False,
        physical_graviton_measured=False)

if __name__=='__main__':
    import sys,time
    kw=json.loads(sys.argv[1]) if len(sys.argv)>1 else {}
    t=time.time();d=propagate(**kw)
    print(json.dumps(d,indent=2));print('elapsed_s',time.time()-t)
