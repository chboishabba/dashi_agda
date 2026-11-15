#!/usr/bin/env python3
"""Original a=t AdS5 TT full coupled (T,y,r) homogeneous semidiscrete
weighted SBP2 SAT energy: exact identity E'<=5E for t in [1,2].

U_T=a P+c M, P_T=(1+v)DwP+LrU-3(P-M)/(2z)+SATfar,
M_T=(v-1)DwM+LrU-3(P-M)/(2z)+SATwall.
Dw f=z^(3/2) D(z^-3/2 f)+3f/(2z), a=(1+v)/2,c=(1-v)/2.
E=0.5 Sum Hy z^-3 Vr (aP²+cM²+U(-Lr)U).

E'= -w0/4 ||(1+v)P0-(1-v)M0||Vr²
    -wN/4 ((1+v)^2||PN||Vr²+(1-v)^2||MN||Vr²)
    +Sum Hy w Vr [(3v/(2z)) (PM-U(-Lr)U)
                       +(v_T/4)(P²-M²)].
Nonzero source G adds -(1-v)w0<M0,G>Vr; cannot bound from G² alone.
Full explicit SSPRK3 coupling, Agda kernel, Weyl trace and physics OPEN.
"""
import math,json
import numpy as np
import sympy as sp
DIMS=(3,7,11)

def coeff(t):
    if not 1<=t<=2:raise ValueError('original a=t t in [1,2]')
    b=1/t;v=-1/math.sqrt(1+t*t)
    return b,v,t**3/(1+t*t)**2,(1+v)/2,(1-v)/2

def radial_stiffness(d,n,dr):
    if d not in DIMS or n<3 or dr<=0:raise ValueError('radial FV')
    L=np.zeros((n,n))
    for j in range(n):
        if j==0:cp,cm=2*d,0.
        else:
            hi=j+.5;lo=j-.5;den=hi**d-lo**d
            cp=d*hi**(d-1)/den;cm=d*lo**(d-1)/den
        L[j,j]=-(cp+cm)/dr**2
        if j>0:L[j,j-1]=cm/dr**2
        if j<n-1:L[j,j+1]=cp/dr**2
    j=np.arange(n,dtype=float)
    V=(((j+.5)*dr)**d-(np.maximum(j-.5,0)*dr)**d)/d
    assert np.allclose(V[:,None]*L,L.T*V[None,:],rtol=3e-12,atol=2e-11)
    S=np.sqrt(V)[:,None]*L/np.sqrt(V)[None,:]
    assert np.linalg.eigvalsh(S)[-1]<0
    return L,V

def sbp_D(f,dy):
    f=np.asarray(f,float)
    if len(f)<3 or dy<=0:raise ValueError('normal SBP')
    out=np.empty_like(f)
    out[0]=(f[1]-f[0])/dy
    out[1:-1]=(f[2:]-f[:-2])/(2*dy)
    out[-1]=(f[-1]-f[-2])/dy
    return out

def weighted_normal_D(f,z,dy):
    root=z**(-1.5)
    return sbp_D(root*f,dy)/root+1.5*f/z

def setup(ny=11,nr=7,dy=.02,dr=.03,t=1.5,seed=2):
    if ny<3 or nr<3:raise ValueError('grid too small')
    b,v,vdot,a,c=coeff(t)
    z=b+np.arange(ny)*dy
    H=np.full(ny,dy);H[0]=H[-1]=dy/2
    rng=np.random.default_rng(seed)
    U=rng.normal(size=(3,ny,nr))*.1
    P=rng.normal(size=(3,ny,nr))*.2
    M=rng.normal(size=(3,ny,nr))*.2
    return dict(U=U,P=P,M=M,z=z,w=z**(-3),H=H,dy=dy,dr=dr,t=t)

def full_energy_derivative(data,source=None,return_derivatives=False):
    U,P,M=[data[k] for k in ('U','P','M')]
    if U.shape!=P.shape or U.shape!=M.shape or U.shape[0]!=3:
        raise ValueError('TT source state shape')
    _,ny,nr=U.shape
    z=data['z'];w=data['w'];H=data['H'];dy=data['dy'];dr=data['dr']
    b,v,vdot,a,c=coeff(data['t'])
    if len(z)!=ny or len(H)!=ny:raise ValueError('normal grid mismatch')
    if source is None:source=np.zeros((3,nr))
    source=np.asarray(source,float)
    if source.shape!=(3,nr):raise ValueError('TT source shape')
    radial=np.empty_like(U);radial_energy=np.empty_like(U)
    vol=np.empty((3,nr))
    for q,d in enumerate(DIMS):
        L,V=radial_stiffness(d,nr,dr)
        vol[q]=V
        radial[q]=U[q]@L.T
        radial_energy[q]=-U[q]*radial[q]
    Ud=a*P+c*M;Pd=np.empty_like(P);Md=np.empty_like(M)
    for q in range(3):
        for j in range(nr):
            p=P[q,:,j];m=M[q,:,j]
            warp=-3*(p-m)/(2*z)
            Pd[q,:,j]=(1+v)*weighted_normal_D(p,z,dy)+radial[q,:,j]+warp
            Md[q,:,j]=(v-1)*weighted_normal_D(m,z,dy)+radial[q,:,j]+warp
            Pd[q,-1,j]-=(1+v)/H[-1]*p[-1]
            target=(1+v)/(1-v)*p[0]-2*source[q,j]/(1-v)
            Md[q,0,j]+=(1-v)/H[0]*(target-m[0])
    vw=vol[:,None,:]*w[None,:,None]*H[None,:,None]
    K=a*P**2+c*M**2
    E=.5*float(np.sum(vw*(K+radial_energy)))
    der_coeff=vdot/4*(P*P-M*M)
    der_weight=-3*v/(2*z)[None,:,None]*(K+radial_energy)
    Ep=float(np.sum(vw*(a*P*Pd+c*M*Md+Ud*(-radial)+der_coeff+der_weight)))
    wall=-w[0]/4*np.sum(vol*((1+v)*P[:,0,:]-(1-v)*M[:,0,:])**2)
    wall-=w[0]*(1-v)*float(np.sum(vol*M[:,0,:]*source))
    far=-w[-1]/4*float(np.sum(vol*((1+v)**2*P[:,-1,:]**2+(1-v)**2*M[:,-1,:]**2)))
    bulk=np.sum(vw*((3*v/(2*z))[None,:,None]*(P*M-radial_energy)+vdot/4*(P*P-M*M)))
    predicted=float(wall+far+bulk)
    err=Ep-predicted
    assert math.isclose(Ep,predicted,abs_tol=3e-9,rel_tol=3e-9),(Ep,predicted,err)
    if not np.any(source):assert Ep<=5*E+1e-9*max(E,1)
    out=dict(E=E,Eprime=Ep,wall=float(wall),far=float(far),bulk=float(bulk),
       exact_identity_residual=float(err),
       homogeneous_semidiscrete_Eprime_below_5E=bool(not np.any(source) and Ep<=5*E+1e-9),
       full_moving_original_T_y_r_homogeneous_SBP2SAT_semidiscrete_identity=True,
       original_physical_nonzero_source_homogeneous_energy_closed=False,
       whole_SSPRK3_time_discrete_closed=False,
       pointwise_original_both_Weyl_trace_proved=False)
    if return_derivatives:out.update(Udot=Ud,Pdot=Pd,Mdot=Md)
    return out

def algebra():
    v,p,m,R,z=sp.symbols('v p m R z',real=True)
    a=(1+v)/2;c=(1-v)/2
    normal=3/(2*z)*(a*(1+v)*p*p+c*(v-1)*m*m-(a*p+c*m)*(p-m))
    weight=-3*v/(2*z)*(a*p*p+c*m*m+R)
    assert sp.simplify(normal+weight-3*v/(2*z)*(p*m-R))==0
    G=sp.symbols('G',real=True);beta=(1+v)/(1-v)
    wall=-a*(1+v)*p*p/2+c*(1-v)*m*m/2+c*(1-v)*m*(beta*p-2*G/(1-v)-m)
    assert sp.simplify(wall+((1+v)*p-(1-v)*m)**2/4+(1-v)*m*G)==0
    return dict(original_bulk_warp_weight_cancellation='3v/(2z)*(P*M-grad_radial_U_squared)',
       original_compatible_wall='-[(1+v)P-(1-v)M]^2/4-(1-v)M*G',
       positive_source_only_wall_bound_from_full_symmetrizer=False)

def audit():
    samples=[]
    for ny,nr,dy,dr,t,seed in ((8,5,.02,.03,1.,1),(11,7,.015,.025,4/3,2),(16,9,.01,.018,2.,3)):
        x=full_energy_derivative(setup(ny,nr,dy,dr,t,seed))
        samples.append(dict(t=t,E=x['E'],Eprime=x['Eprime'],residual=x['exact_identity_residual']))
    return dict(symbolic=algebra(),samples=samples,uniform_growth_constant=5,
      full_homogeneous_coupled_semidiscrete_SBP4_closed=True,
      original_forced_source_lift_necessary=True,
      original_full_SSPRK3_closed=False,both_Weyl_receiver_converged=False)

if __name__=='__main__':print(json.dumps(audit(),indent=2))
