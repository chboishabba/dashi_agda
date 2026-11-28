"""Signed coefficient error transport on the original event and Cayley chart.
Bounds are real-arithmetic candidates, not outward-rounded certification.
"""
import numpy as np


def checked_error(e):
    e=np.asarray(e,float)
    if e.shape!=(3,) or not np.isfinite(e).all() or np.any(e<0):
        raise ValueError('invalid three-fibre error radius')
    return e


def event_difference_coefficients(N,R,A):
    """Homogeneous normalized-current map through order s^2, u=s^2.
    Arrays shape (3, species), rows are u^0,u^1,u^2 coefficients.
    Higher-order terms multiplying uninhabited current coefficients are zero
    on the licensed finite-velocity domain, not a global padded derivative.
    """
    N,R,A=map(lambda v:np.asarray(v,float),(N,R,A))
    if N.ndim!=2 or N.shape[0]!=3 or N.shape!=R.shape or N.shape!=A.shape:
        raise ValueError('event coefficient shape')
    F=N-R; M=F+A
    for v in (N,R,A,F,M):
        if not np.isfinite(v).all() or np.any(v[0]<0) or np.any((v[0]==0)&(v[1]<0)) or np.any((v[0]==0)&(v[1]==0)&(v[2]<0)):
            raise ValueError('negative or nonfinite leading event coefficient')
    def valuation(v):
        nz=np.flatnonzero(v);return int(nz[0]) if len(nz) else 3
    C=np.zeros_like(N); old_order=np.array([valuation(v) for v in N.T]);new_order=np.array([valuation(v) for v in M.T])
    for j,(n,m) in enumerate(zip(old_order,new_order)):
        f=valuation(F[:,j])
        if n==3 or m==3 or f==3:continue
        power=2*f-n-m
        if f<max(n,m) or power<0:
            raise ValueError('survival exceeds population valuation')
        if power+n>2:continue
        den=np.sqrt(N[n,j])*np.sqrt(M[m,j])
        C[power,j]=F[f,j]/den
        if power==0 and n==0:
            # Only this case can contribute a second multiplier to x0.
            C[2,j]=(F[1,j]-.5*F[0,j]*(N[1,j]/N[0,j]+M[1,j]/M[0,j]))/den
    if np.any(C[0]<0) or np.any(C[0]>1+1e-12):raise ValueError('noncontractive leading event')
    return np.repeat(C,3,axis=1),np.repeat(old_order,3),np.repeat(new_order,3)


def event_difference(C,old_order,new_order,difference):
    C=np.asarray(C,float);d=np.asarray(difference,float)
    if C.shape!=d.shape or C.shape[0]!=3:raise ValueError('event difference shape')
    if np.any(d[np.arange(3)[:,None]<old_order[None,:]]!=0):
        raise ValueError('uninhabited shadow current coefficient')
    out=np.stack([sum(C[j]*d[k-j] for j in range(k+1)) for k in range(3)])
    if np.any(out[np.arange(3)[:,None]<new_order[None,:]]!=0):
        raise ArithmeticError('event creates uninhabited coefficient')
    return out


def event_error(e,c1,c2):
    a,b,c=checked_error(e)
    if min(c1,c2)<0 or not np.isfinite([c1,c2]).all():raise ValueError('invalid event norm')
    return np.array([a,b+c1*a,c+c1*b+c2*a])


def stage_error(e,h,a1,a2):
    """Same compatible dissipative stage, including lower-order forcing.
    The norm of each resolvent and homogeneous Cayley map is <=1.
    Returns endpoint radius and midpoint radius, not joint contraction.
    """
    a,b,c=checked_error(e)
    if h<=0 or min(a1,a2)<0 or not np.isfinite([h,a1,a2]).all():raise ValueError('invalid stage norm')
    d1=h*a1*a
    d2=h*(a1*(b+d1/2)+a2*a)
    return np.array([a,b+d1,c+d2]),np.array([a,b+d1/2,c+d2/2])


def receiver_error(mid,e,L,Lu,h):
    """Absolute differences of all three receiver work coefficients."""
    mid,L,Lu=map(lambda x:np.asarray(x,float),(mid,L,Lu));e=checked_error(e)
    if mid.shape!=(3,len(L)) or Lu.shape!=L.shape or np.any(L<0) or h<=0:
        raise ValueError('invalid receiver coefficient chart')
    def bilinear(i,j,weights):
        m=np.max(abs(weights),initial=0.)
        return m*(np.linalg.norm(mid[i])*e[j]+np.linalg.norm(mid[j])*e[i]+e[i]*e[j])
    return h*np.array([bilinear(0,0,L),2*bilinear(0,1,L),
        bilinear(1,1,L)+2*bilinear(0,2,L)+bilinear(0,0,Lu)])


def residual_coefficients(actual,shadow,lifted,propagated):
    actual,shadow,lifted=map(lambda x:np.asarray(x,float),(actual,shadow,lifted))
    if actual.shape!=shadow.shape or actual.shape!=lifted.shape or actual.shape[0]!=3:
        raise ValueError('unaligned signed coefficient residuals')
    p=checked_error(propagated);r=shadow-lifted;err=actual-lifted
    observed=np.linalg.norm(actual-shadow,axis=1);scale=np.maximum(1.,np.linalg.norm(actual,axis=1)+np.linalg.norm(shadow,axis=1))
    if np.any(observed>p+1e-10*scale):raise ArithmeticError('triangular propagation bound failed')
    bound=p+np.linalg.norm(r,axis=1)
    if np.any(np.linalg.norm(err,axis=1)>bound+1e-10*scale):raise ArithmeticError('signed residual bound failed')
    return dict(signed_step_residual=r.tolist(),signed_endpoint_error=err.tolist(),
        observed_propagation_error=observed.tolist(),endpoint_error=np.linalg.norm(err,axis=1).tolist(),
        error_bound_candidate=bound.tolist(),outward_rounding_certified=False)
