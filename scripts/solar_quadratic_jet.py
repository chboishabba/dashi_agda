"""Coefficient (not factorial derivative) transport in u=s^2, s>=0.
Original reaction/event/Cayley owners retain the primal. These functions
supply the missing second amplitude coefficient and fourth density coefficient.
"""
import numpy as np
from scipy.linalg import solve

def mul(a,b):
    return np.stack([sum(a[j]*b[k-j] for j in range(k+1)) for k in range(3)])

def exp_fraction(a):
    """1-exp(a), with a[0]<=0, stable at zero."""
    e=np.exp(a[0])
    return np.stack([-np.expm1(a[0]),-e*a[1],-e*(a[2]+a[1]**2/2)])

def reaction_u2(n,pool,T,p,h,q,n_u,pool_u,T_u,p_u,n_uu,pool_uu):
    """Coefficient u^2 of original reaction, T and p affine in u."""
    alpha=np.asarray(q['recombination_m3_s'],float)
    k=np.asarray(q['ionization_s_inv'],float)
    g=np.asarray(q['heater_ionization_per_J'],float)
    Q=np.asarray(q.get('activation_temperature_K',[0.,0.]),float)
    N=np.stack([n,n_u,n_uu]); P=np.stack([pool,pool_u,pool_uu])
    r=mul(N[:,1:],exp_fraction(-h*N[:,0,None]*alpha))
    avail=P+r
    e=k*np.exp(-Q/T); t1=Q*T_u/T**2; t2=-Q*T_u**2/T**3
    rate=np.stack([e+g*p,e*t1+g*p_u,e*(t2+t1*t1/2)])
    a=mul(avail,exp_fraction(-h*rate))
    return np.r_[r[2].sum(),r[2]],np.r_[a[2].sum(),a[2]],(avail-a)[2]

def amplitude2(n,nu,nuu):
    """s^2 coefficient of sqrt(n+u*nu+u^2*nuu+o(u^2))."""
    n,nu,nuu=map(lambda a:np.asarray(a,float),(n,nu,nuu))
    if not all(np.isfinite(a).all() for a in (n,nu,nuu)):
        raise ValueError('nonfinite amplitude jet')
    if np.any(n<0) or np.any((n==0)&(nu<0)) or np.any((n==0)&(nu==0)&(nuu<0)):
        raise ValueError('negative leading population')
    out=np.zeros_like(n); pos=n>0; higher=(n==0)&(nu==0)
    out[pos]=nu[pos]/(2*np.sqrt(n[pos]))
    out[higher]=np.sqrt(nuu[higher])
    return out

def event_state2(z,z1,z2,n,r,a,n_u,r_u,a_u,n_uu,r_uu,a_uu,b,signed_mass):
    """Second s coefficient of original normalized-current event.
    signed_mass = sign(charge)*sqrt(volume*mass). Bounded velocity path;
    zero coefficients cannot be replaced by an arbitrary nonzero velocity.
    """
    z,z1,z2,b=map(lambda v:np.asarray(v,float).reshape(3,3),(z,z1,z2,b))
    N=np.stack([n,n_u,n_uu]); R=np.stack([r,r_u,r_uu]); A=np.stack([a,a_u,a_uu])
    F=N-R; M=F+A
    for p in (N,R,A,F,M): amplitude2(*p)
    out=np.zeros_like(z)
    for j in range(3):
        n0,n1,n2=N[:,j]; m0,m1,m2=M[:,j]
        w=signed_mass[j]
        v=np.zeros((3,3))
        if n0>0:
            root=np.sqrt(n0)
            v[0]=z[j]/(w*root); v[1]=z1[j]/(w*root)
            v[2]=z2[j]/(w*root)-n1/(2*n0)*v[0]
        elif n1>0:
            if np.any(z[j]!=0): raise ValueError('uninhabited base current')
            v[0]=z1[j]/(w*np.sqrt(n1)); v[1]=z2[j]/(w*np.sqrt(n1))
        elif n2>0:
            if np.any(z[j]!=0) or np.any(z1[j]!=0): raise ValueError('uninhabited lower jet')
            v[0]=z2[j]/(w*np.sqrt(n2))
        elif np.any(z[j]!=0) or np.any(z1[j]!=0) or np.any(z2[j]!=0):
            raise ValueError('uninhabited current jet')
        f0,f1,f2=F[:,j]; a0,a1,a2=A[:,j]
        if m0>0:
            p0=f0*v[0]+a0*b[j]
            p2=f0*v[2]+f1*v[0]+a1*b[j]
            out[j]=w/np.sqrt(m0)*(p2-m1/(2*m0)*p0)
        elif m1>0:
            out[j]=w*f1*v[1]/np.sqrt(m1)
        elif m2>0:
            out[j]=w*(f2*v[0]+a2*b[j])/np.sqrt(m2)
    return out.ravel()

def cayley2(P,A1,A2,x2,y1,x1,mid0,h,b2):
    """Second coefficient on a compatible right-limit stage."""
    I=np.eye(len(x2)); mid1=(x1+y1)/2
    return solve(I-h*P/2,(I+h*P/2)@x2+h*(A1@mid1+A2@mid0+b2))

def work2(x,x1,x2,L,Lu):
    return float(x1@(L*x1)+2*x@(L*x2)+x@(Lu*x))

def squared_return2(endpoint,original,first,second):
    return [float(np.sum(a*a)+2*np.sum((x-o)*b))
            for x,o,a,b in zip(endpoint,original,first,second)]
