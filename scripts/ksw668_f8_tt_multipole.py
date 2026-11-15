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

@njit(cache=True)
def stage(U,P,M,outU,outP,outM,dr,dy,b,v,amplitude,sources,cp,cm):
    nm,ny,nr=U.shape
    d2=dr*dr
    for q in range(nm):
        d=3+4*q
        for iy in range(ny):
            z=b+iy*dy
            for ir in range(nr):
                p=P[q,iy,ir] if iy<ny-1 else 0.
                m=M[q,iy,ir]
                if iy==0:
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
                if iy==ny-1:
                    outP[q,iy,ir]=0.
                elif iy<ny-2:
                    outP[q,iy,ir]=(1+v)*(-3*p+4*P[q,iy+1,ir]-P[q,iy+2,ir])/(2*dy)+force
                else:
                    outP[q,iy,ir]=(1+v)*(P[q,iy+1,ir]-p)/dy+force
                if iy==0:
                    outM[q,iy,ir]=0.
                elif iy>1:
                    outM[q,iy,ir]=(v-1)*(3*m-4*M[q,iy-1,ir]+M[q,iy-2,ir])/(2*dy)+force
                else:
                    outM[q,iy,ir]=(v-1)*(m-M[q,iy-1,ir])/dy+force

@njit(cache=True)
def enforce(U,P,M,v,amp,sources):
    M[:,0,:]=(2*amp*sources-(1+v)*P[:,0,:])/(v-1)
    P[:,-1,:]=0
    U[:,:,-1]=0;P[:,:,-1]=0;M[:,:,-1]=0

def F(t):return math.asinh(t)-math.sqrt(1+t*t)/t

def propagate(dr=.008,dy=.012,dt=.0015,eps=.04,final_t=12,
              pulse=.065,inside_chord=.012,r_outer=4.3,y_outer=3.0,drive=1.):
    if not(2<final_t<=20 and 0<dr<eps/3 and 0<dy<=.03
            and 0<dt<min(dr*.45,dy*.45) and 0<eps<.08
            and r_outer>3 and y_outer>2 and 0<pulse<.12):
        raise ValueError('positive original-model parameters / resolved source')
    T0,Tend=F(1),F(final_t)
    span=Tend-T0
    bulk=math.sqrt(span*span-(1-1/final_t)**2)
    rx=bulk-inside_chord
    gap=rx-eps-math.log(final_t)
    if gap<=0:raise ValueError('receiver inside brane photon cone')
    nr=int(math.ceil(r_outer/dr))+1
    ny=int(math.ceil(y_outer/dy))+1
    rg=np.arange(nr)*dr
    src=normalized_sources(eps,rg)
    cp=np.zeros((3,nr));cm=np.zeros((3,nr))
    for q in range(3):
        ell=2*q
        for j in range(1,nr):
            cp[q,j]=(1+.5/j)**(2+2*ell)
            cm[q,j]=(1-.5/j)**(2+2*ell)
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
    for it in range(nt):
        T=T0+it*dt
        v,b,amp=coeff(T)
        enforce(U,P,M,v,amp,src)
        stage(U,P,M,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm)
        U1[:]=U+dt*dU;P1[:]=P+dt*dP;M1[:]=M+dt*dM
        v,b,amp=coeff(T+dt)
        enforce(U1,P1,M1,v,amp,src)
        stage(U1,P1,M1,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm)
        U2[:]=.75*U+.25*(U1+dt*dU)
        P2[:]=.75*P+.25*(P1+dt*dP)
        M2[:]=.75*M+.25*(M1+dt*dM)
        v,b,amp=coeff(T+dt/2)
        enforce(U2,P2,M2,v,amp,src)
        stage(U2,P2,M2,dU,dP,dM,dr,dy,b,v,amp,src,cp,cm)
        U[:]=(U+2*(U2+dt*dU))/3
        P[:]=(P+2*(P2+dt*dP))/3
        M[:]=(M+2*(M2+dt*dM))/3
    def read(r):
        # Evaluate SAME physical receiver radius at every grid resolution.
        x=r/dr;ir=int(math.floor(x));frac=x-ir
        if ir<1 or ir+2>=nr:raise ValueError('receiver interior to grid')
        weights=np.array([-frac*(frac-1)*(frac-2)/6,
                           (frac+1)*(frac-1)*(frac-2)/2,
                          -(frac+1)*frac*(frac-2)/2,
                           (frac+1)*frac*(frac-1)/6])
        modes=[float((r/eps)**(2*j)*np.dot(weights,U[j,0,ir-1:ir+3]))
               for j in range(3)]
        return r,modes,sum(modes)
    rr,components,yy=read(rx)
    far,fc,fy=read(bulk+.1)
    return dict(model='original moving AdS5 a=t Neumann compact TT',
        original_radial_multipoles=[0,2,4],
        effective_radial_dimensions=[3,7,11],
        step_radial=dr,step_bulk=dy,step_time=dt,
        radius_bins=nr,bulk_bins=ny,steps=nt,
        eps=eps,pulse=pulse,receiver_t=final_t,
        nominal_receiver_r=rx,receiver_grid_r=rr,
        source_adjusted_brane_photon_margin=gap,
        raw_mode_values=components,
        retarded_TT_yy_scaled_by_eps4=yy,
        far_receiver_grid_r=far,far_mode_values=fc,
        far_TT_yy_scaled_by_eps4=fy,
        fixed_physical_receiver_cubic_interpolation=True,
        no_post_evolution_spatial_derivatives=True,
        no_spatial_Fourier_Bessel_inverse=True,
        compact_support_of_boundary_stress=True,
        numerical_convergence_certified=False,
        full_Weyl_receiver_certified=False,
        Agda_kernel_accepted=False,
        physical_graviton_measured=False)

if __name__=='__main__':
    import sys,time
    kw=json.loads(sys.argv[1]) if len(sys.argv)>1 else {}
    t=time.time();d=propagate(**kw)
    print(json.dumps(d,indent=2));print('elapsed_s',time.time()-t)
