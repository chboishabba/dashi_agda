"""Original G3 harmonic reduced Ricci finite-box comparator; not a validated PDE.
Classical harmonic Einstein reduction, no damping or physical boundary claim.
"""
import numpy as np
from math import comb
from scipy.integrate import solve_ivp


def run(n,R=.25,end=.02,div=8):
    e=.25; dx=2*R/(n-1); x=np.linspace(-R,R,n)
    X=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1); a,b,c=np.moveaxis(X,-1,0); r2=np.sum(X*X,axis=-1)
    sol=solve_ivp(lambda r,y:[y[1],-16*e*e*y[0]/(3*(1+r*r)**4)],(0,64),(0.,1.),rtol=2e-12,atol=2e-14)
    assert sol.success
    coeff=[1.]
    for j in range(20):
        coeff.append(-16*e*e/3*sum((-1)**k*comb(k+3,3)*coeff[j-k] for k in range(j+1))/((2*j+2)*(2*j+3)))
    q=(np.polynomial.polynomial.polyval(r2,coeff)/sol.y[1,-1])**2
    A=2*e*np.stack([2*a*c-2*b,2*a+2*b*c,1-a*a-b*b+c*c],axis=-1)/(1+r2)[...,None]**2
    g=np.zeros(X.shape[:-1]+(5,5)); g[...,0,0]=-1
    g[...,1:4,1:4]=q[...,None,None]*(np.eye(3)+A[..., :,None]*A[...,None,:]); g[...,4,1:4]=g[...,1:4,4]=q[...,None]*A; g[...,4,4]=q
    v=np.zeros_like(g); interior=(slice(2,-2),)*3
    def diff(f,i):
        return (np.roll(f,-1,axis=i-1)-np.roll(f,1,axis=i-1))/(2*dx) if 1<=i<=3 else np.zeros_like(f)
    def first(g,v):
        return np.stack([v]+[diff(g,i) for i in range(1,5)],axis=-3)
    def conn(g,dg):
        inv=np.linalg.inv(g)
        L=(np.swapaxes(dg,-3,-2)+np.swapaxes(dg,-3,-1)-dg)/2 # L[a,i,j]= (d_i g_aj+d_j g_ia-d_a g_ij)/2
        C=np.einsum('...ab,...bij->...aij',inv,L)
        return inv,L,C
    inv,L,C=conn(g,first(g,v))
    lower=np.einsum('...ij,...aij->...a',inv,L)
    # C_i initially equals spatial contracted connection minus v_0i.
    v[...,0,1:]=v[...,1:,0]=lower[...,1:]
    def rhs(g,v):
        dg=first(g,v); inv,L,C=conn(g,dg)
        dd=np.stack([first(v,np.zeros_like(v))]+[diff(dg,i) for i in range(1,5)],axis=-4)
        di=-np.einsum('...ab,...kbc,...cd->...kad',inv,dg,inv)
        dL=(np.swapaxes(dd,-3,-2)+np.swapaxes(dd,-3,-1)-dd)/2
        dC=np.einsum('...kab,...bij->...kaij',di,L)+np.einsum('...ab,...kbij->...kaij',inv,dL)
        Ric=np.einsum('...aaij->...ij',dC)-np.einsum('...jaia->...ij',dC)+np.einsum('...aab,...bij->...ij',C,C)-np.einsum('...ajb,...bia->...ij',C,C)
        Cl=np.einsum('...ij,...aij->...a',inv,L)
        dCl=np.einsum('...kij,...aij->...ka',di,L)+np.einsum('...ij,...kaij->...ka',inv,dL)
        nab=dCl-np.einsum('...aij,...a->...ij',C,Cl)
        reduced=Ric-(nab+np.swapaxes(nab,-1,-2))/2
        # R_ab - nabla_(a C_b) = -g^00 g_ab,tt/2 + known terms.
        acc=2*reduced/inv[...,0,0,None,None]
        outg=np.zeros_like(g); outv=np.zeros_like(v)
        outg[interior]=v[interior];outv[interior]=((acc+np.swapaxes(acc,-1,-2))/2)[interior]
        return outg,outv
    def diagnostic(g,v):
        inv,L,C=conn(g,first(g,v)); cl=np.einsum('...ij,...aij->...a',inv,L)
        mask=np.max(abs(X),axis=-1)<=.08+1e-12
        return np.sqrt(np.mean(np.sum(cl[mask]**2,axis=-1))),np.max(abs(cl[mask]))
    initial=diagnostic(g,v); assert initial[1]<1e-12
    steps=int(np.ceil(end/(dx/div)));dt=end/steps; mid=(n//2,)*3
    for _ in range(steps):
        a,b=rhs(g,v); c,d=rhs(g+dt*a/2,v+dt*b/2); f,h=rhs(g+dt*c/2,v+dt*d/2); j,l=rhs(g+dt*f,v+dt*h)
        g+=dt*(a+2*c+2*f+j)/6;v+=dt*(b+2*d+2*h+l)/6
        assert np.min(np.linalg.eigvalsh(g[...,1:,1:]))>0 and np.max(np.linalg.inv(g)[...,0,0])<0
    final=diagnostic(g,v); H=g[mid]; q=H[4,4]; receiver=(H[3,4]/q,np.sqrt(q),H[3,3]-H[3,4]**2/q)
    print('n,R,steps',n,R,steps,'harmonic C initial',initial,'final',final,'central KK spatial',receiver,flush=True)
    return final,receiver

if __name__=='__main__':
    for n,R,d in ((9,.25,8),(13,.25,8),(13,.375,8)):
        run(n,R,div=d)
    print('Completed harmonic reduced evolution diagnostics; no continuum acceptance')
