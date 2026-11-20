"""Moving geometric pairing and stage attribution for projected F8 SSPRK3.
Reuse warp_stage_adjoint.transpose; not a coupled energy certificate.
"""
import numpy as np

def metric(ny,nr,dr,dy,b):
    if min(ny,nr)<2 or min(dr,dy,b)<=0: raise ValueError('invalid geometry')
    r=np.arange(nr-1)*dr
    mu=np.array([((r+dr/2)**d-np.maximum(r-dr/2,0)**d)/d for d in (3,7,11)])
    h=np.full(ny,dy);h[[0,-1]]*=.5
    w=mu[:,None,:]*(h/(b+dy*np.arange(ny))**3)[None,:,None]
    return np.broadcast_to(w,(3,)+w.shape)

def project(x):
    x=x.copy();x[..., -1]=0;return x

def lower(lam,w):
    p=np.zeros_like(lam);p[..., :-1]=lam[..., :-1]*w;return p

def raise_dual(p,w):
    lam=np.zeros_like(p);lam[..., :-1]=p[..., :-1]/w;return lam

def reverse(p,AT,BT,CT):
    p=project(p);p2=2*CT(p)/3;p1=BT(p2)/4
    return project(p/3+3*p2/4+AT(p1)),(p1,p2/4,2*p/3)

def weighted_reverse(lam,w0,w1,AT,BT,CT):
    p,dual=reverse(lower(lam,w1),AT,BT,CT)
    return raise_dual(p,w0),dual

def source_ledger(dual,insertions):
    """Three stages, then physical mode and spatial cell; signed, not alpha."""
    return np.stack([np.sum(project(p)*project(r),axis=0) for p,r in zip(dual,insertions,strict=True)])

def native_reverse(lam,w0,w1,dr,dy,h,geometry,order):
    from warp_stage_adjoint import transpose
    def make(b,v):
        return lambda p:project(p+h*transpose(p,dr,dy,b,v,order))
    return weighted_reverse(lam,w0,w1,*(make(*g) for g in geometry))

def check():
    rng=np.random.default_rng(1530);shape=(3,3,4,5);n=np.prod(shape)
    w0=metric(4,5,.2,.3,.7);w1=metric(4,5,.2,.3,.6)
    x=project(rng.normal(size=shape));lam=project(rng.normal(size=shape))
    A,B,C=[np.eye(n)+rng.normal(size=(n,n))*.01 for _ in range(3)]
    def op(a):return lambda x:project((a@project(x).ravel()).reshape(shape))
    a,b,c=map(op,(A,B,C));at,bt,ct=map(op,(A.T,B.T,C.T))
    r=[project(rng.normal(size=shape)) for _ in range(3)]
    x1=a(x)+r[0];x2=.75*x+.25*(b(x1)+r[1]);y=x/3+2*(c(x2)+r[2])/3
    adj,dual=weighted_reverse(lam,w0,w1,at,bt,ct)
    ledger=source_ledger(dual,r)
    lhs=np.sum(lower(lam,w1)*y);rhs=np.sum(lower(adj,w0)*x)+ledger.sum()
    np.testing.assert_allclose(lhs,rhs,rtol=1e-12,atol=1e-12)
    assert np.all(w0>0) and not np.allclose(w0[:,0],w0[:,1])
    assert np.all(raise_dual(lower(x,w0),w0)[...,-1]==0)
    np.testing.assert_allclose(raise_dual(lower(x,w0),w0),x)
    print('PASS synthetic projected moving metric and affine three-stage ledger',lhs,rhs,abs(lhs-rhs))
if __name__=='__main__':check()
