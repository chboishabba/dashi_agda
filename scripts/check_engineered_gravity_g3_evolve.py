"""Original G3 Gaussian ADM finite-difference interior comparator.
Finite box, frozen boundary, no continuum or well-posedness certificate.
"""
import numpy as np
from math import comb
from scipy.integrate import solve_ivp

def run(n):
    e=.25; R=.25; dx=2*R/(n-1); x=np.linspace(-R,R,n)
    X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1); a,b,c=np.moveaxis(X,-1,0); r2=np.sum(X*X,axis=-1)
    sol=solve_ivp(lambda r,y:[y[1],-16*e*e*y[0]/(3*(1+r*r)**4)],(0,64),(0.,1.),rtol=2e-12,atol=2e-14)
    assert sol.success
    coeff=[1.]
    for j in range(20):
        coeff.append(-16*e*e/3*sum((-1)**k*comb(k+3,3)*coeff[j-k] for k in range(j+1))/((2*j+2)*(2*j+3)))
    p=np.polynomial.polynomial.polyval(r2,coeff)/sol.y[1,-1]; q=p*p
    A=2*e*np.stack([2*a*c-2*b,2*a+2*b*c,1-a*a-b*b+c*c],axis=-1)/(1+r2)[...,None]**2
    h=np.zeros(X.shape[:-1]+(4,4)); h[...,:3,:3]=q[...,None,None]*(np.eye(3)+A[..., :,None]*A[...,None,:]); h[...,3,:3]=h[...,:3,3]=q[...,None]*A; h[...,3,3]=q
    K=np.zeros_like(h); interior=(slice(2,-2),)*3
    def diff(f,i):
        return (np.roll(f,-1,axis=i)-np.roll(f,1,axis=i))/(2*dx) if i<3 else np.zeros_like(f)
    def geom(g):
        inv=np.linalg.inv(g); dg=np.stack([diff(g,i) for i in range(4)],axis=-3)
        # C^a_ij = inverse contracted with metric derivative combination
        C=np.empty(g.shape[:-2]+(4,4,4))
        for i in range(4):
            for j in range(4):
                C[..., :,i,j]=np.einsum('...ab,...b->...a',inv,dg[...,i,:,j]+dg[...,j,:,i]-dg[..., :,i,j])/2
        Ric=np.zeros_like(g)
        for i in range(4):
            for j in range(4):
                for a in range(4):
                    Ric[...,i,j]+=diff(C[...,a,i,j],a)-diff(C[...,a,i,a],j)
                    for b in range(4):
                        Ric[...,i,j]+=C[...,a,a,b]*C[...,b,i,j]-C[...,a,j,b]*C[...,b,i,a]
        return inv,(Ric+np.swapaxes(Ric,-1,-2))/2,C
    def rhs(g,k):
        inv,Ric,_=geom(g); tr=np.einsum('...ij,...ji->...',inv,k)
        dg=np.zeros_like(g); dk=np.zeros_like(k)
        dg[interior]=-2*k[interior]; dk[interior]=(Ric+tr[...,None,None]*k-2*k@inv@k)[interior]
        return dg,dk
    mid=(n//2,)*3
    def diag(g,k):
        inv,Ric,C=geom(g); mixed=inv@k; tr=np.trace(mixed,axis1=-2,axis2=-1)
        H=np.einsum('...ij,...ji->...',inv,Ric)+tr*tr-np.trace(mixed@mixed,axis1=-2,axis2=-1)
        M=np.zeros(g.shape[:-2]+(4,))
        for i in range(4):
            M[...,i]=-diff(tr,i)
            for j in range(4):
                M[...,i]+=diff(mixed[...,j,i],j)
                for l in range(4):
                    M[...,i]+=C[...,j,j,l]*mixed[...,l,i]-C[...,l,j,i]*mixed[...,j,l]
        return float(abs(H[mid])),float(np.max(abs(M[mid])))
    initial=diag(h,K); h0=h[mid].copy(); end=.04; steps=int(np.ceil(end/(dx/8))); dt=end/steps
    for _ in range(steps):
        a,b=rhs(h,K); c,d=rhs(h+dt*a/2,K+dt*b/2); f,g=rhs(h+dt*c/2,K+dt*d/2); j,l=rhs(h+dt*f,K+dt*g)
        h+=dt*(a+2*c+2*f+j)/6; K+=dt*(b+2*d+2*g+l)/6
        assert np.min(np.linalg.eigvalsh(h))>0
    final=diag(h,K); H=h[mid]; A=H[2,3]/H[3,3]; phi=np.sqrt(H[3,3]); base=H[2,2]-H[2,3]**2/H[3,3]
    print('n',n,'steps',steps,'initial H/M',initial,'final H/M',final,'receiver',A,phi,base,flush=True)
    return np.array([A,phi,base]),initial,final

if __name__=='__main__':
    results=[run(n) for n in (13,17,25)]
    assert results[-1][1][0]<results[0][1][0]
    assert np.linalg.norm(results[2][0]-results[1][0])<np.linalg.norm(results[1][0]-results[0][0])
    print('PASS finite-box interior evolution and selected refinement; no continuum acceptance')
