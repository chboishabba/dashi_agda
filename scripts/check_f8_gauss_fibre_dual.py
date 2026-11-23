"""Discrete time-fibre residual attribution for the unchanged geometric receiver.
Coarse collocation path is sampled at fine times (even nonnested meshes).
Each fine step residual is paired with the exact fine discrete adjoint.
Finite small-grid regression, not an original-resolution error certificate.
"""
import argparse
import numpy as np
from check_f8_gauss_banded import BandedGauss
from check_f8_gauss_fibre import stages
from check_f8_gauss_action import b,c


def run(n=12,ne=3,p=2,h=.02):
    C=BandedGauss(n,ne,p,h);F=BandedGauss(n,ne,p,h/2)
    assert C.t==F.t and C.r==F.r and np.array_equal(C.src,F.src)
    x=np.zeros((2,C.fe.n,C.n)); states=[]; deriv=[]
    for i in range(C.nt):
        states.append(x.copy());K=stages(C,x,i);deriv.append(K)
        x+=C.dt*np.einsum('s,sunm->unm',b,K)
    end=x.copy()
    def sample(j):
        if j==F.nt:return end
        i,r=divmod(j*C.nt,F.nt);theta=r/F.nt
        integ=np.array([(theta*theta/2-c[1]*theta)/(c[0]-c[1]),(theta*theta/2-c[0]*theta)/(c[1]-c[0])])
        return states[i]+C.dt*np.einsum('s,sunm->unm',integ,deriv[i])
    fine=F.forward();W,_,_=F.weights();Cw,_,_=C.weights()
    assert all(np.array_equal(W[k],Cw[k]) for k in W)
    L=np.stack([F.flat(F.terminal(w)) for w in W.values()],axis=-1)
    # Source vanishes at the common terminal fibre, so terminal jets are linear.
    assert F.stage[2*F.nt][-1]==0
    modal=np.zeros((4,n,len(W)));abssum=np.zeros((n,len(W)))
    for j in range(F.nt-1,-1,-1):
        r=sample(j+1)-F.advance(sample(j),j)
        contrib=np.einsum('md,mdr->mr',F.flat(r),L)
        modal[min(3,4*j//F.nt)]+=contrib;abssum+=abs(contrib)
        L,_=F.reverse_flat(L,j)
    expected=np.array([np.sum(w*(C.jets(end)-F.jets(fine)),axis=(0,1)) for w in W.values()]).T
    got=modal.sum(axis=0)
    err=np.linalg.norm(got-expected)/max(np.linalg.norm(abssum),1e-300)
    assert err<1e-8,(err,got,expected)
    print('grid',n,ne,p,'coarse/fine steps',C.nt,F.nt,'closure',err,flush=True)
    for k,name in enumerate(W):
        print(name,'difference',expected[:,k].sum(),'attributed',got[:,k].sum(),'time quarters',modal[:,:,k].sum(axis=1),'mode quarters',[got[idx,k].sum() for idx in np.array_split(np.arange(n),4)],flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--grid',nargs=4,default=['12','3','2','.02']);args=parser.parse_args().grid
    run(*(tuple(map(int,args[:3]))+(float(args[3]),)))
