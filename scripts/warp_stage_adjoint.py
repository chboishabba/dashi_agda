"""Transpose of original KSW668 stage, normal_order 3/4, on projected states."""
import numpy as np
from scipy.sparse import csr_matrix
from functools import lru_cache

@lru_cache(maxsize=32)
def radial(nr,dr,q):
    d=3+4*q
    R=np.zeros((nr,nr)); R[0,:2]=[-2*d,2*d]
    j=np.arange(1,nr-1); den=(j+.5)**d-(j-.5)**d
    p=d*(j+.5)**(d-1)/den; m=d*(j-.5)**(d-1)/den
    R[j,j-1]=m; R[j,j]=-p-m; R[j,j+1]=p
    return csr_matrix(R/dr**2)

@lru_cache(maxsize=4096)
def normal(ny,dy,b,order):
    D=np.zeros((ny,ny)); D[0,:2]=[-1,1]; D[-1,-2:]=[-1,1]
    j=np.arange(1,ny-1); D[j,j-1]=-.5; D[j,j+1]=.5; D/=dy
    z=b+dy*np.arange(ny)
    if order==4: D=z[:,None]**1.5*D*z[None,:]**-1.5+np.diag(1.5/z)
    return csr_matrix(D)

def transpose(y,dr,dy,b,v,order):
    assert order in (3,4)
    y=y.copy(); y[..., -1]=0
    out=np.zeros_like(y); _,nm,ny,nr=y.shape
    D=normal(ny,dy,b,order); z=b+dy*np.arange(ny); a=1+v;c=1-v
    for q in range(nm):
        U,P,M=y[:,q]; S=P+M
        out[0,q]=(radial(nr,dr,q).T@S.T).T
        out[1,q]=a*U/2+a*(D.T@P)-1.5*S/z[:,None]
        out[2,q]=c*U/2-c*(D.T@M)+1.5*S/z[:,None]
        out[1,q,-1]-=2*a*P[-1]/dy
        out[1,q,0]+=2*a*M[0]/dy
        out[2,q,0]-=2*c*M[0]/dy
    out[..., -1]=0
    return out

def donor_parity():
    from ksw668_f8_tt_multipole import stage
    rng=np.random.default_rng(1530); nm,ny,nr=3,7,11; dr,dy,b,v=.008,.012,.4,-.3
    cp=np.zeros((nm,nr));cm=cp.copy()
    for q in range(nm):
        d=3+4*q;j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d;cp[q,1:]=d*(j+.5)**(d-1)/den;cm[q,1:]=d*(j-.5)**(d-1)/den
    for order in (3,4):
        x=rng.normal(size=(3,nm,ny,nr));x[..., -1]=0;y=rng.normal(size=x.shape); out=np.zeros_like(x)
        stage(*x,*out,dr,dy,b,v,0.,np.zeros((nm,nr)),cp,cm,order)
        lhs=np.vdot(out,y);rhs=np.vdot(x,transpose(y,dr,dy,b,v,order));assert np.isclose(lhs,rhs,rtol=1e-12,atol=1e-8)
        print(order,lhs,rhs,abs(lhs-rhs))
if __name__=='__main__':donor_parity()
