import numpy as np
from numba import njit

@njit(cache=True)
def transpose_into(x,out,rad,normal,v,z):
    _,nm,ny,nr=x.shape
    a=1+v;c=1-v
    for q in range(nm):
        for i in range(ny):
            for j in range(nr-1):
                u,p,m=x[0,q,i,j],x[1,q,i,j],x[2,q,i,j]
                rr=0.;dp=0.;dm=0.
                for k in range(3):
                    jj=j+k-1;ii=i+k-1
                    if 0<=jj<nr-1:rr+=rad[q,j,k]*(x[1,q,i,jj]+x[2,q,i,jj])
                    if 0<=ii<ny:
                        dp+=normal[i,k]*x[1,q,ii,j]
                        dm+=normal[i,k]*x[2,q,ii,j]
                pp=a*u/2+a*dp-1.5*(p+m)/z[i]
                mm=c*u/2-c*dm+1.5*(p+m)/z[i]
                if i==ny-1:pp-=2*a*p/(z[1]-z[0])
                if i==0:
                    pp+=2*a*m/(z[1]-z[0]);mm-=2*c*m/(z[1]-z[0])
                out[0,q,i,j]=rr;out[1,q,i,j]=pp;out[2,q,i,j]=mm
            out[:,q,i,-1]=0

def bands(A):
    n=len(A); out=np.zeros((n,3))
    for k in range(3):
        i=np.arange(max(0,1-k),min(n,n+1-k));out[i,k]=A[i,i+k-1]
    return out

def radial_bands(nr,dr):
    from warp_stage_adjoint import radial
    return np.array([bands(radial(nr,dr,q).T.toarray()) for q in range(3)])

def normal_bands(ny,dy,b,order):
    from warp_stage_adjoint import normal
    return bands(normal(ny,dy,b,order).T.toarray()),b+dy*np.arange(ny)

def check():
    import sympy as s
    from warp_stage_adjoint import transpose
    z,w,d=s.symbols('z w d',positive=True)
    assert s.simplify((z/w)**s.Rational(3,2)*d-z**s.Rational(3,2)*d*w**(-s.Rational(3,2)))==0
    rng=np.random.default_rng(1530)
    for order in (3,4):
        for ny,nr in [(7,11),(68,252),(251,539)]:
            dr=.008;dy=.012;b=.4;v=-.3
            rad=radial_bands(nr,dr);normal,z=normal_bands(ny,dy,b,order)
            x=rng.normal(size=(3,3,ny,nr));x[..., -1]=0;out=np.empty_like(x)
            transpose_into(x,out,rad,normal,v,z)
            ref=transpose(x,dr,dy,b,v,order)
            np.testing.assert_allclose(out,ref,rtol=1e-11,atol=1e-8)
            print(order,ny,nr,np.max(abs(out-ref)),flush=True)
if __name__=='__main__':check()
