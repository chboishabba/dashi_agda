"""Fixed-physical-receiver polynomial stencil sensitivity (one mode)."""
import numpy as np
from math import sqrt
from warp_kernel_refinement_audit import native_setup,adjoint_bank


def e4_observation(s,q,npoints):
    assert npoints in (4,6,8)
    dr=s['dr'];r=s['rx'];h=s['h'];nt=s['nt'];tf=s['final_t'];eps=s['eps']
    ir=int(r/dr);offset=np.arange(1-npoints//2,1+npoints//2);indices=ir+offset
    assert indices[0]>=0 and indices[-1]<len(s['r'])-1
    delta=offset-(r/dr-ir);A=delta[None,:]**np.arange(npoints)[:,None]
    rhs=np.zeros((npoints,3));rhs[0,0]=1;rhs[1,1]=1/dr;rhs[2,2]=2/dr**2
    w,dw,dd=np.linalg.solve(A,rhs).T
    np.testing.assert_allclose(A@np.stack((w,dw,dd),axis=1),rhs,atol=1e-8,rtol=1e-10)
    ell=2*q;pref=-(r/eps)**ell/(4*tf**2);S=sqrt(1+tf**2)/tf;Se=-1/(tf*sqrt(1+tf**2))
    spatial=dd+2*ell*dw/r+ell*(ell-1)*w/r**2
    o=np.zeros_like(s['obs'][0:1,:,:,q:q+1])
    for i,sign in enumerate((-1,0,1)):
        o[0,i,0,0,0,indices]=pref*w*(S*S*(1 if sign else -2)/h**2+Se*sign/(2*h))
        if sign==0:o[0,i,0,0,0,indices]+=pref*spatial
    return o


def check(q=0,**params):
    s=native_setup(setup_only=True,**params);o=e4_observation(s,q,4)
    np.testing.assert_allclose(o,s['obs'][0:1,:,:,q:q+1],rtol=1e-10,atol=1e-8)
    obs=np.concatenate((o,e4_observation(s,q,6)),axis=0)
    g=adjoint_bank(obs,s['h'],s['dy'],s['RT'][q:q+1],s['coeff'],s['src'][None,q:q+1],s['active'])[0]
    t=s['t'];h=s['h'];_,v,b,*_=s['coeff'];w=np.zeros_like(t)
    for n in range(s['nt']+1):w[2*n:2*n+3]+=h*np.array([1/6,2/3,1/6])
    w/=(-v*b**3);G=(g/w)@g.T;C=G.diagonal()
    print('mode',q,'cubic/quintic compliance',C,'ratio',C[1]/C[0],
          'cosine',G[0,1]/np.sqrt(C[0]*C[1]),'relative L2',np.sqrt(np.sum((g[0]-g[1])**2/w)/C[1]),flush=True)
    return C

if __name__=='__main__':
    import json,sys
    check(**json.loads(sys.argv[1]))
