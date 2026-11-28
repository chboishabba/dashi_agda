"""Driven Gauss reference on original normalized Whitney coordinates.
Local vacuum sweeps, shifted electric work chart; implicit material reference.
No physical light cone or simultaneous energy claim for staggered branch.
"""
import numpy as np
from scipy.linalg import solve


def staggered_metric(C,h):
    ne=C.shape[1];nf=C.shape[0]
    return np.block([[np.eye(ne),-h*C.T/2],[-h*C/2,np.eye(nf)]])


def driven_step(C,J,R,p,u,x,h,mode='staggered'):
    """J skew electric/current generator, R passive loss, p incident port.
    x=(E,B,current); J,R,p have only E/current coordinates, no B.
    Port convention f=p*u-p*p.T*w, reflected u-p.T*w*2 (see ledger).
    Here incident wave is u/2, outgoing u/2-p.T*w.
    """
    nf,ne=C.shape;n=len(x);idx=np.r_[np.arange(ne),np.arange(ne+nf,n)]
    J,R,p=map(np.asarray,(J,R,p));x=np.asarray(x);p=p.reshape(-1)
    if h<=0 or J.shape!=R.shape or J.shape!=(len(idx),len(idx)) or p.shape!=(len(idx),):raise ValueError('chart')
    if not np.array_equal(J,-J.T) or not np.array_equal(R,R.T) or np.linalg.eigvalsh(R).min()<0:raise ValueError('passivity')
    H=J-R-np.outer(p,p)
    if mode=='staggered':
        if h*np.linalg.norm(C)>=2:raise ValueError('CFL certificate')
        y=x.copy();y[ne:ne+nf]-=h*C@x[:ne];y[:ne]+=h*C.T@y[ne:ne+nf]
        shift=h*C.T@y[ne:ne+nf]/2;w=y[idx].copy();w[:ne]-=shift
        mid=solve(np.eye(len(idx))-h*H/2,w+h*p*u/2)
        delta=h*(H@mid+p*u);y[idx]+=delta
        G=np.eye(n);G[:ne+nf,:ne+nf]=staggered_metric(C,h)
        charge_delta=delta[:ne]
    elif mode=='implicit':
        A=np.zeros((n,n));A[:ne,ne:ne+nf]=C.T;A[ne:ne+nf,:ne]=-C;A[np.ix_(idx,idx)]=H
        src=np.zeros(n);src[idx]=p*u
        m=solve(np.eye(n)-h*A/2,x+h*src/2);y=x+h*(A@m+src);mid=m[idx];G=np.eye(n)
        charge_delta=h*(H@mid+p*u)[:ne]
    else:raise ValueError('mode')
    loss=h*(mid@R@mid);port=h*((u/2)**2-(u/2-p@mid)**2)
    change=(y@G@y-x@G@x)/2
    return y,dict(energy_change=change,loss=loss,port=port,residual=change+loss-port,charge_delta=charge_delta,work_electric=mid[:ne],physical_admission=False,mode=mode)


def native_test():
    from solar_spherical_geometry import geometry
    from solar_spherical_material_weld import construct
    v,mesh,ne,nf=geometry([1.,1.2],0);n=len(v);z=np.ones((n,3));axis=np.tile([0.,0.,1.],(n,1))
    model=construct([1.,1.2],0,np.arange(n),v,z*1e-12,z*2,z*3,axis)
    A=model['exchange'];C=-A[ne:ne+nf,:ne];idx=np.r_[np.arange(ne),np.arange(ne+nf,len(A))];J=A[np.ix_(idx,idx)];R=model['loss'][np.ix_(idx,idx)].copy();R[0,0]+=.04
    p=np.zeros(len(idx));p[0]=.2;me,mb=model['energy_masses'];d0,d1,d2=model['incidence'];Qe=d0.T*np.sqrt(me);Qb=d2/np.sqrt(mb);Qe/=np.linalg.norm(Qe,axis=1)[:,None];Qb/=np.linalg.norm(Qb,axis=1)[:,None]
    rng=np.random.default_rng(369);x=rng.normal(size=len(A))*1e-5;out={}
    for mode,h in [('staggered',.5/np.linalg.norm(C)),('implicit',.001)]:
        y=x.copy();q=Qe@y[:ne];b=Qb@y[ne:ne+nf];err=0
        for k in range(5):
            y,r=driven_step(C,J,R,p,.2,y,h,mode);q+=Qe@r['charge_delta'];err=max(err,abs(r['residual']))
        qe=np.linalg.norm(Qe@y[:ne]-q);qb=np.linalg.norm(Qb@y[ne:ne+nf]-b)
        assert err<1e-12 and qe<1e-10 and qb<1e-10,(mode,err,qe,qb)
        out[mode]=dict(energy_residual=err,electric_continuity=qe,magnetic_gauss=qb,step_s=h)
    return out

if __name__=='__main__':print(native_test())
