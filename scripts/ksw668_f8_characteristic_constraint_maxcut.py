#!/usr/bin/env python3
"""KSW original a=t moving AdS5 TT: physical characteristic constraint cut IX.

C=D_y U-(P-M)/2 with P=H_T+H_z, M=H_T-H_z. Original a=(1+v)/2,
c=(1-v)/2, v=-1/sqrt(1+t²). For the SECOND ORDER UNWEIGHTED SBP-SAT
scheme normal_order=3, the actual Numba stage has C'_j=0 at EVERY
interior normal node even for the nonzero prescribed Israel wall source.
Therefore every explicit SSPRK3 convex stage exactly preserves the
interior constraint, for arbitrary time-dependent moving coefficients.

The AdS-weighted split form normal_order=4 instead has C'_int =
 a*(D-Dw)P + c*(D-Dw)M, generically nonzero for a finite mesh.
Its defect is O(dy²) for smooth interior data but can be large on rough
grid functions; homogeneous weighted energy alone is insufficient.

Exact finite-grid commutator: the symmetric part of H*w*(D-Dw) has
 diagonal -H_i*w_i*3/(2*z_i) and edge (w_i-w_{i+1})/4.
For 0<dy<=b/4, its H*w operator norm <=4/b via Gershgorin,
hence original mode3 full coupled weighted semidiscrete E'_3 <=
(5+16*t)*E_3, for t>=1, b=1/t. The actual weak SAT endpoints
remain an independent boundary-constraint obligation.

Lift the ORIGINAL nonzero Israel datum G by
Lambda_M=-2G(T,r)*chi(y)/(1-v), Lambda_U=Lambda_P=0.
The same mode3 has the genuinely sourced full coupled estimate
Etilde'_3 <=(6+16*t)*Etilde_3+0.5*||F||_E²,
with F_U=c*Lambda_M, F_P=3 Lambda_M/(2z),
F_M=(v-1) D Lambda_M+3 Lambda_M/(2z)-d_T Lambda_M.
The weighted F norm includes the radial gradient of F_U.
Neither estimate is a full coupled SSPRK3 energy theorem or Weyl trace.
"""
import math, json
import numpy as np
from ksw668_f8_full_coupled_weighted_sbp_energy import (
    setup,coeff,sbp_D,weighted_normal_D,radial_stiffness)
from ksw668_f8_tt_multipole import stage,enforce

DIMS=(3,7,11)
def D_y(A,dy):
    return np.stack([np.stack([sbp_D(A[q,:,j],dy)
        for j in range(A.shape[2])],axis=-1)
        for q in range(A.shape[0])],axis=0)
def D_w(A,z,dy):
    return np.stack([np.stack([weighted_normal_D(A[q,:,j],z,dy)
        for j in range(A.shape[2])],axis=-1)
        for q in range(A.shape[0])],axis=0)
def physical_constraint(U,P,M,dy):
    return D_y(U,dy)-.5*(P-M)
def actual_stage(data,mode=3,G=None):
    U,P,M=[np.pad(data[k],((0,0),(0,0),(0,1)))
           for k in ('U','P','M')]
    _,ny,nr=U.shape
    if mode not in (3,4):raise ValueError('only weak SAT 3 or 4')
    if G is None:G=np.zeros((3,nr-1))
    src=np.pad(np.asarray(G,float),((0,0),(0,1)))
    b,v,_,_,_=coeff(data['t'])
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate(DIMS):
        for j in range(1,nr):
            hi=j+.5;lo=j-.5;den=hi**d-lo**d
            cp[q,j]=d*hi**(d-1)/den
            cm[q,j]=d*lo**(d-1)/den
    out=[np.empty_like(U) for _ in range(3)]
    enforce(U,P,M,v,1.,src,mode)
    stage(U,P,M,*out,data['dr'],data['dy'],b,v,1.,src,cp,cm,mode)
    return tuple(x[:,:,:-1].copy() for x in out)

def energy_derivative(data,rhs):
    U,P,M=[data[k] for k in ('U','P','M')]
    dU,dP,dM=rhs
    _,v,vt,a,c=coeff(data['t'])
    R=np.empty_like(U);Re=np.empty_like(U);V=[]
    for q,d in enumerate(DIMS):
        L,vr=radial_stiffness(d,U.shape[-1],data['dr'])
        R[q]=U[q]@L.T;Re[q]=-U[q]*R[q];V.append(vr)
    vw=np.array(V)[:,None,:]*data['H'][None,:,None]*data['w'][None,:,None]
    K=a*P*P+c*M*M
    E=.5*float(np.sum(vw*(K+Re)))
    Eprime=float(np.sum(vw*(a*P*dP+c*M*dM-dU*R+
        vt/4*(P*P-M*M)-3*v/(2*data['z'])[None,:,None]*(K+Re))))
    return E,Eprime

def compare(t=4/3,ny=13,nr=7,dy=.015,dr=.03,seed=51):
    data=setup(ny=ny,nr=nr,dy=dy,dr=dr,t=t,seed=seed)
    rhs3=actual_stage(data,3);rhs4=actual_stage(data,4)
    _,v,_,a,c=coeff(t)
    cdot3=D_y(rhs3[0],dy)-.5*(rhs3[1]-rhs3[2])
    cdot4=D_y(rhs4[0],dy)-.5*(rhs4[1]-rhs4[2])
    defect=a*(D_y(data['P'],dy)-D_w(data['P'],data['z'],dy))
    defect+=c*(D_y(data['M'],dy)-D_w(data['M'],data['z'],dy))
    assert np.max(abs(cdot3[:,1:-1,:]))<1e-9
    assert np.max(abs(cdot4[:,1:-1,:]-defect[:,1:-1,:]))<1e-9
    E3,Ep3=energy_derivative(data,rhs3)
    E4,Ep4=energy_derivative(data,rhs4)
    vw=np.stack([radial_stiffness(d,nr,dr)[1] for d in DIMS])[:,None,:]
    vw=vw*data['H'][None,:,None]*data['w'][None,:,None]
    comm=float(np.sum(vw*(a*(1+v)*data['P']*
            (D_y(data['P'],dy)-D_w(data['P'],data['z'],dy))
           +c*(v-1)*data['M']*
            (D_y(data['M'],dy)-D_w(data['M'],data['z'],dy)))))
    assert abs((Ep3-Ep4)-comm)<1e-9
    return dict(t=t,Ny=ny,Nr=nr,
        unweighted_mode3_interior_Cdot=float(np.max(abs(cdot3[:,1:-1,:]))),
        weighted_mode4_interior_Cdot=float(np.max(abs(cdot4[:,1:-1,:]))),
        weighted_commutator_identity_residual=(Ep3-Ep4)-comm,
        E=E3,Eprime_mode3=Ep3,
        mode3_constraint_exact_interior=True,
        mode3_weak_boundary_constraint_open=True,
        mode4_constraint_exact_interior=False)

def normal_commutator_certificate(t,Ny,dy):
    b,_,_,_,_=coeff(t)
    if not(Ny>=4 and 0<dy<=b/4):raise ValueError('dy<=b/4 needed')
    z=b+np.arange(Ny)*dy;w=z**(-3)
    H=np.full(Ny,dy);H[0]=H[-1]=dy/2
    edge=(w[:-1]-w[1:])/(4*np.sqrt(H[:-1]*w[:-1]*H[1:]*w[1:]))
    T=np.diag(-3/(2*z))+np.diag(edge,1)+np.diag(edge,-1)
    rowsum=3/(2*z)+np.r_[edge[0],edge[:-1]+edge[1:],edge[-1]]
    lam=float(np.max(abs(np.linalg.eigvalsh(T))))
    assert lam<=max(rowsum)+1e-10
    assert max(rowsum)<=4/b+1e-10
    # Verify finite-grid formula matches actual weighted derivative.
    x=np.random.default_rng(Ny).normal(size=Ny)
    observed=float(np.dot(H*w*x,sbp_D(x,dy)-weighted_normal_D(x,z,dy)))
    xw=np.sqrt(H*w)*x
    assert math.isclose(observed,float(xw@T@xw),rel_tol=2e-11,abs_tol=2e-11)
    return dict(t=t,dy=dy,Ny=Ny,
        measured_quadratic_operator_norm=lam,
        Gershgorin_bound=float(max(rowsum)),
        proven_analytic_uniform_bound=4/b,
        mode3_coupled_Eprime_over_E_bound=5+16*t)

def rk3_constraint_step(t0=4/3,dt=.0005,ny=11,nr=6,dy=.012,dr=.025):
    data=setup(t=t0,ny=ny,nr=nr,dy=dy,dr=dr,seed=79)
    data['M']=data['P']-2*D_y(data['U'],dy)
    original=physical_constraint(data['U'],data['P'],data['M'],dy)
    assert np.max(abs(original))<1e-12
    G=np.stack([.02*np.exp(-(np.arange(nr)*dr/.08)**2)*(q+1)
        for q in range(3)])
    def rhs(X,t,s,mode):
        return actual_stage(dict(data,U=X[0],P=X[1],M=X[2],t=t),mode,s*G)
    # Use actual ORIGINAL Poincare-stage clock T=F(t), not arbitrary t offsets.
    from scipy.optimize import brentq
    from ksw668_f8_tt_multipole import F
    T0=F(t0)
    tmid=brentq(lambda t:F(t)-(T0+dt/2),t0,t0+.2)
    tnext=brentq(lambda t:F(t)-(T0+dt),t0,t0+.2)
    out={}
    for mode in (3,4):
        X=[data[k].copy() for k in ('U','P','M')]
        one=[x+dt*y for x,y in zip(X,rhs(X,t0,1,mode))]
        two=[.75*x+.25*(a+dt*b) for x,a,b in
            zip(X,one,rhs(one,tnext,1.3,mode))]
        final=[x/3+2*(a+dt*b)/3 for x,a,b in
            zip(X,two,rhs(two,tmid,.6,mode))]
        dc=physical_constraint(*final,dy)-original
        out[mode]=dict(interior=float(np.max(abs(dc[:,1:-1,:]))),
                       boundary=float(np.max(abs(dc[:,[0,-1],:]))))
    assert out[3]['interior']<1e-10
    assert out[4]['interior']>1e-5
    return out

def smooth_drift(dy):
    t=4/3;b,_,_,a,c=coeff(t)
    z=b+np.arange(round(.3/dy)+1)*dy
    P=np.cos(3*z)+.2*np.sin(4*z)
    M=.7*np.sin(2*z)-.3*np.cos(5*z)
    delta=a*(sbp_D(P,dy)-weighted_normal_D(P,z,dy))
    delta+=c*(sbp_D(M,dy)-weighted_normal_D(M,z,dy))
    return float(max(abs(delta[2:-2])))

def forced_source_lift(t=4/3,ny=11,nr=7,dy=.012,dr=.025,seed=4):
    from ksw668_f8_full_coupled_source_lift import chi_compact
    data=setup(t=t,ny=ny,nr=nr,dy=dy,dr=dr,seed=seed)
    b,v,vt,a,c=coeff(t)
    rng=np.random.default_rng(seed+777)
    G=rng.normal(size=(3,nr))*.02
    GT=rng.normal(size=(3,nr))*.01
    chi=chi_compact(np.arange(ny)*dy,dy*6)
    Lam=-2*chi[None,:,None]*G[:,None,:]/(1-v)
    LamT=-2*chi[None,:,None]*(GT[:,None,:]/(1-v)+
        G[:,None,:]*vt/(1-v)**2)
    full=dict(data,M=data['M']+Lam)
    Ud,Pd,Md=actual_stage(full,3,G)
    Ud0,Pd0,Md0=actual_stage(data,3)
    FU=c*Lam;FP=3*Lam/(2*data['z'][None,:,None])
    FM=np.stack([np.stack([
        (v-1)*sbp_D(Lam[q,:,j],dy)+
        3*Lam[q,:,j]/(2*data['z'])-LamT[q,:,j]
        for j in range(nr)],axis=-1) for q in range(3)])
    err=max(np.max(abs(Ud-Ud0-FU)),np.max(abs(Pd-Pd0-FP)),
        np.max(abs(Md-Md0-LamT-FM)))
    assert err<1e-9
    V=[];RFU=[]
    for q,d in enumerate(DIMS):
        L,vq=radial_stiffness(d,nr,dr)
        V.append(vq);RFU.append(FU[q]@L.T)
    vw=np.array(V)[:,None,:]*data['H'][None,:,None]*data['w'][None,:,None]
    RFU=np.array(RFU)
    fnorm=float(np.sum(vw*(a*FP*FP+c*FM*FM-FU*RFU)))
    E,Ep=energy_derivative(data,(Ud0,Pd0,Md0))
    work=float(np.sum(vw*(a*data['P']*FP+c*data['M']*FM-data['U']*RFU)))
    upper=(6+16*t)*E+.5*fnorm
    assert Ep+work<=upper+1e-8*max(1,upper)
    Cdot=D_y(Ud,dy)-.5*(Pd-Md)
    assert np.max(abs(Cdot[:,1:-1,:]))<1e-9
    return dict(t=t,source_lift_operator_error=float(err),
        interior_constraint_Cdot=float(np.max(abs(Cdot[:,1:-1,:]))),
        energy_derivative=Ep+work,
        forced_energy_bound=upper,
        sourced_coupled_semidiscrete_energy_and_constraint_closed=True,
        fully_discrete_coupled_SSPRK3_energy_open=True,
        both_Weyl_receiver_error_open=True)

def audit():
    rows=[compare(t,ny=ny,nr=nr,dy=dy,dr=dr,seed=seed)
       for t,ny,nr,dy,dr,seed in
       [(1.,9,5,.015,.025,8),(4/3,13,7,.012,.025,17),
        (2.,17,9,.01,.02,23),(12.,12,6,.009,.02,45)]]
    bound=[normal_commutator_certificate(t,13,(1/t)/d)
       for t in (1.,4/3,2.,12.) for d in (32,16,8,4)]
    h=[.04,.02,.01,.005];smooth=[smooth_drift(x) for x in h]
    assert all(smooth[i]/smooth[i+1]>3.7 for i in range(3))
    forced=[forced_source_lift(t) for t in (1.,4/3,2.,12.)]
    return dict(original_model='a=t moving AdS5 compact TT characteristic',
       measured_original_slices=rows,
       explicit_normal_commutator_Gershgorin_certificates=bound,
       smooth_weighted_constraint_defect=smooth,
       actual_RK3_stage_constraint_test=rk3_constraint_step(),
       full_coupled_original_sourced_lift_checks=forced,
       mode3_physical_interior_constraint_exact=True,
       source_lifted_mode3_Eprime_bound='(6+16t)E+0.5||F||², dy<=b/4',
       global_weak_Israel_constraint_weld_accepted=False,
       full_explicit_RK3_coupled_energy_accepted=False,
       both_Weyl_curvature_convergence_accepted=False,
       experimental_graviton_accepted=False)
if __name__=='__main__':print(json.dumps(audit(),indent=2))
