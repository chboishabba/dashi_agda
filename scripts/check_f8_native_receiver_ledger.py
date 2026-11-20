"""Receiver-time attribution on original SSPRK3 computational fibres.
Donor observations are native Cartesian stencil channels, NOT full tensor E4/E5.
Short window regression, no production-duration or continuum claim.
"""
import numpy as np
from warp_temporal_weighted_adjoint import run as setup
from ksw668_f8_tt_multipole import stage
from warp_frame_attribution import project, metric, lower, raise_dual, native_reverse

def check(order=4, **params):
    s=setup(order=order,setup_only=True,**params)
    dr,dy,h,nt,src=(s[k] for k in ('dr','dy','h','nt','src'))
    _,vel,b,*_=s['coeff']
    obs=s['obs']
    shape=obs.shape[2:]
    nr,ny=shape[-1],shape[-2]
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den
        cm[q,1:]=d*(j-.5)**(d-1)/den
    def geom(k):return b[k],vel[k]
    def W(k):return metric(ny,nr,dr,dy,b[k])
    def euler(x,k,f=0.):
        out=np.empty_like(x)
        stage(*x,*out,dr,dy,*geom(k),f,src,cp,cm,order)
        return project(x+h*out)
    def step(x,n,rs):
        k=2*n
        u=euler(x,k)+rs[0]
        v=.75*x+.25*(euler(u,k+2)+rs[1])
        return u,v,x/3+2*(euler(v,k+1)+rs[2])/3
    # Last two steps span all three original time injections. Random initial
    # state and independent signed sources are deliberate finite controls.
    first=nt-1;last=nt+1
    rng=np.random.default_rng(1530+order)
    x0=project(rng.normal(size=shape)*1e-4)
    x=x0.copy();states=[x.copy()];records=[]
    for n in range(first,last):
        k=2*n
        ks=(k,k+2,k+1)
        rs=[euler(np.zeros(shape),j,f) for j,f in zip(ks,(.013,-.021,.034))]
        u,v,y=step(x,n,rs)
        # Observation cut crosses a normal node; distinct from physical flux.
        threshold=(b[k]+b[k+2])/2+2*dy
        masks=[(b[j]+dy*np.arange(ny))[None,None,:,None]<threshold
               for j in (k,k+2,k+1,k+2)]
        Q0,QA,QB,Q1=masks
        A=lambda z:euler(z,k)
        B=lambda z:euler(z,k+2)
        C=lambda z:euler(z,k+1)
        ka=QA*A(x)-A(Q0*x)
        kb=QB*B(u)-B(QA*u)
        kc=Q1*C(v)-C(QB*v)
        terms=(C(B(ka))/6,C(kb)/6,2*kc/3,
               C((QB.astype(float)-Q0)*x)/2,(Q1.astype(float)-Q0)*x/3)
        _,_,base=step(Q0*x,n,[m*r for m,r in zip(masks[1:],rs)])
        np.testing.assert_allclose(Q1*y-base,sum(terms),rtol=1e-9,atol=1e-9)
        records.append((rs,masks,terms))
        x=y;states.append(x.copy())
    # One continuous mask family is needed for regional telescoping.
    # Per-step cut thresholds differ, so retain explicit handoff residuals.
    for ch in range(4):
        p=project(obs[ch,2]);initial=None
        signed=np.zeros((2,3,3));interface=np.zeros((2,5,3))
        regional=np.zeros((2,3,3));handoff=np.zeros(3)
        def bymode(a,b):return np.sum(a*b,axis=(0,2,3))
        for i in (1,0):
            n=first+i;k=2*n
            rs,masks,terms=records[i]
            adj,dual=native_reverse(raise_dual(p,W(k+2)),W(k),W(k+2),
                                    dr,dy,h,tuple(map(geom,(k,k+2,k+1))),order)
            for j,(d,r,m) in enumerate(zip(dual,rs,masks[1:])):
                signed[i,j]=bymode(d,r)
                regional[i,j]=bymode(d,m*r)
            for j,t in enumerate(terms):interface[i,j]=bymode(p,t)
            pprev=lower(adj,W(k))
            if i==1:
                handoff=bymode(pprev,(masks[0].astype(float)-records[0][1][-1])*states[1])
            p=pprev+project(obs[ch,i])
        actual=sum(bymode(project(o),x) for o,x in zip(obs[ch],states))
        initial=bymode(p,states[0])
        def assert_ledger(actual,expected,scale):
            assert np.all(np.abs(actual-expected)<=1e-8*np.maximum(1.,scale)),(actual,expected)
        assert_ledger(actual,initial+signed.sum(axis=(0,1)),
                      np.abs(initial)+np.abs(signed).sum(axis=(0,1)))
        region_masks=[records[0][1][0],records[0][1][-1],records[1][1][-1]]
        retained=sum(bymode(project(o),m*x) for o,m,x in zip(obs[ch],region_masks,states))
        expected=bymode(p,region_masks[0]*states[0])+regional.sum(axis=(0,1))+interface.sum(axis=(0,1))+handoff
        scale=np.abs(bymode(p,region_masks[0]*states[0]))+np.abs(regional).sum(axis=(0,1))+np.abs(interface).sum(axis=(0,1))+np.abs(handoff)
        assert_ledger(retained,expected,scale)
        print('order',order,'channel',ch,'actual',actual,'retained',retained,
              'source signed',signed.sum(axis=(0,1)),'interface signed',interface.sum(axis=(0,1)),
              'handoff',handoff,flush=True)

if __name__=='__main__':
    import sys,json
    params=json.loads(sys.argv[1]) if len(sys.argv)>1 else {}
    for order in (3,4):check(order,**params)
