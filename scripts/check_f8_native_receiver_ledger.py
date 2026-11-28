"""Receiver-time attribution on original SSPRK3 computational fibres.
Default observations are legacy native Cartesian stencil channels. Opt-in geometric diagnostic uses independently reconstructed wall jets; no strong trace claim.
Short window regression, no production-duration or continuum claim.
"""
import numpy as np
from warp_temporal_weighted_adjoint import run as setup
from ksw668_f8_weighted_normal_stage import matched_stage as stage
from warp_frame_attribution import project, metric, lower, raise_dual, native_reverse

def check(order=4, geometric=False, **params):
    s=setup(order=order,setup_only=True,**params)
    dr,dy,h,nt,src=(s[k] for k in ('dr','dy','h','nt','src'))
    _,vel,b,*_=s['coeff']
    obs=s['obs']
    shape=obs.shape[2:]
    nr,ny=shape[-1],shape[-2]
    if geometric:
        from warp_native_geometric_receiver import receiver_bank
        obs=receiver_bank(s['final_t'],s['rx'],s['eps'],dr,dy,h,vel,nt,nr,ny)
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
    receipts=[]
    for ch in range(len(obs)):
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
        receipts.append((actual,retained,initial,signed,regional,interface,handoff))
        print('order',order,'channel',ch,'actual',actual,'retained',retained,
              'source signed',signed.sum(axis=(0,1)),'interface signed',interface.sum(axis=(0,1)),
              'handoff',handoff,flush=True)

    if geometric:
        t=s['final_t']
        for channels in zip(*receipts):
            terms=np.stack((channels[2],-channels[3],(1/t+1/(2*t**3))*channels[4],channels[5]/(3*t*t)))
            assert np.max(np.abs(terms.sum(0)))<=1e-10*max(1.,np.max(np.abs(terms).sum(0)))
        from warp_israel_affine import radial_source_at_receiver, offsets, forced_identity
        # Centre slot is the start of the second synthetic step (amplitude .013).
        # Receiver is outside source support in the original guarded setup.
        dg=radial_source_at_receiver(src,1.,s['rx'],s['eps'],dr)
        g=.013*dg
        actual=np.stack([r[0] for r in receipts]);forced=actual+offsets(g)
        err,scale=forced_identity(forced,g,t)
        assert np.all(np.abs(err)<=1e-10*np.maximum(1.,scale))
        # Shared centre event: step 0 B and step 1 A use the same time slot.
        # Synthetic stage amplitudes remain independent; the direct receiver
        # control is explicitly owned by step 1 A, not by both stages.
        unit=euler(np.zeros(shape),2*nt,1.)
        # Source contributions were stored with amplitude .013 for step 1 A.
        propagated=np.stack([r[3][1,0]/.013 for r in receipts])
        direct=offsets(dg)
        delta=1e-4
        _,_,perturbed=step(states[1],nt,[records[1][0][0]+delta*unit,*records[1][0][1:]])
        finite=np.array([bymode(project(o[2]),perturbed-states[2])/delta for o in obs])+direct
        np.testing.assert_allclose(finite,propagated+direct,rtol=1e-6,atol=1e-6)
        # Receiver offset ownership is at the physical wall node, not the
        # derivative stencil or the number of stages touching the event.
        owner=float(region_masks[1][0,0,0,0]); regional_offset=owner*offsets(g)
        complement_offset=(1-owner)*offsets(g)
        np.testing.assert_array_equal(regional_offset+complement_offset,offsets(g))
        print('forced wall receiver',forced[4],'prescribed source offset',-g,
              'direct gradient',direct[4],'regional offset',regional_offset[4],flush=True)
        print('PASS off-shell identity through all signed ledger channels',flush=True)

if __name__=='__main__':
    import sys,json
    params=json.loads(sys.argv[1]) if len(sys.argv)>1 else {}
    for order in (3,4):check(order,**params)
