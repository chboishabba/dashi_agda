"""Finite-grid reverse endpoint weld with separate signed source/work accounting.
Controller norm is a mathematical objective, not electrical work or hardware cost.
"""
import json
import numpy as np
from solar_earth_spatial_transport import Grid,cell,verify_step
from scipy.optimize import brentq


def lifted(grid,h,steps,controller_ports,observe):
    """Build exact-in-model discrete linear input/state/observation maps by basis replay."""
    p=grid.prepare(h); z=np.zeros(grid.size); eye=np.eye(grid.size)
    A=np.column_stack([grid.step(x,h,p)[0] for x in eye]); L=np.column_stack([grid.step(z,h,p,(x[0],x[1]),(0,0))[0] for x in np.eye(2)])
    B=np.column_stack([grid.step(z,h,p,controller=x)[0] for x in controller_ports.T])
    # Accumulate a declared end-of-step linear receiver observation, not load work.
    AA=np.zeros((grid.size+1,grid.size+1)); AA[:-1,:-1]=A; AA[-1,:-1]=h*observe@A; AA[-1,-1]=1
    def augment(M): return np.vstack([M,h*observe@M])
    def history(M): return np.column_stack([np.linalg.matrix_power(AA,steps-1-k)@M for k in range(steps)])
    return history(augment(L)),history(augment(B)),p


def run(grid,h,p,external,ports,control,observe,factors=None):
    z=np.zeros(grid.size); result=np.zeros(5); y=0.; features=[]
    for f,a in zip(external,control):
        z,w,_=verify_step(grid,z,h,p,f,(0,0),ports@a); y+=h*observe@z
        if factors is not None: features.extend(F@v for F,v in zip(factors,w['material_inputs']))
        result+=np.array([w['exterior_inward'][0],w['exterior_inward'][1],w['controller'],w['material_loss'].sum(),w['load'].sum()])
    N,R,C,Q,W=result; U=z@z/2; res=U+Q+W-N-R-C
    assert abs(res)<1e-10
    return np.r_[z,y],dict(left_inward=float(N),right_inward=float(R),controller=float(C),material_loss=float(Q),load=float(W),stored_final=float(U),net_load_less_controller=float(W-C),balance_residual=float(res)),np.concatenate(features) if factors is not None else None


def maximize_net(g,h,p,external,ports,observe,B,x,radius,rng):
    # Fixed boundary trace: exterior work is affine in the control coordinates;
    # independently integrated material loss is a squared linear feature norm.
    factors=[]
    for _,Q in p[2]:
        val,V=np.linalg.eigh(sum(Q[1:])); assert min(val)>-1e-12
        factors.append(np.sqrt(np.maximum(val,0))[:,None]*V.T)
    n=len(external); dim=len(x)
    def trial(v): return run(g,h,p,external,ports,v.reshape(n,-1),observe,factors)
    target,base,f0=trial(x); assert abs(f0@f0-base['material_loss'])<1e-10
    _,sv,Vh=np.linalg.svd(B,full_matrices=True); rank=int(np.sum(sv>sv[0]*1e-12)); Z=Vh[rank:].T
    assert np.linalg.norm(B@Z)<1e-10 and np.linalg.norm(x@Z)<1e-10
    F=[]; a=[]
    for d in Z.T:
        _,w,f=trial(x+d); F.append(f-f0); a.append(w['left_inward']-base['left_inward'])
    F=np.column_stack(F); a=np.array(a); H=F.T@F; grad=a-2*F.T@f0
    # Concave quadratic in endpoint-null coordinates with an explicit synthetic norm budget.
    ev,V=np.linalg.eigh(H); assert min(ev)>-1e-12; ev=np.maximum(ev,0); ghat=V.T@grad
    positive=ev>max(ev)*1e-12; u=np.zeros_like(ev); u[positive]=ghat[positive]/(2*ev[positive]); lam=0.
    if np.linalg.norm(ghat[~positive])>1e-10 or np.linalg.norm(u)>radius:
        def norm(l): return np.linalg.norm(ghat/(2*ev+l))
        hi=1.
        while norm(hi)>radius: hi*=2
        lam=brentq(lambda l:norm(l)-radius,1e-15,hi,xtol=1e-14); u=ghat/(2*ev+lam)
    d=V@u; endpoint,w,f=trial(x+Z@d)
    pred=base['left_inward']+a@d-np.linalg.norm(f0+F@d)**2
    kkt=np.linalg.norm(grad-2*H@d-lam*d)
    assert kkt<1e-9 and np.linalg.norm(d)<=radius+1e-9 and np.linalg.norm(endpoint-target)<1e-9
    assert abs(pred-w['net_load_less_controller'])<1e-9 and np.linalg.norm(f-f0-F@d)<1e-9
    assert w['net_load_less_controller']>=base['net_load_less_controller']-1e-10
    for _ in range(20):
        v=rng.normal(size=len(d)); v*=radius*rng.random()/np.linalg.norm(v)
        _,sample,_=trial(x+Z@v); assert sample['net_load_less_controller']<=w['net_load_less_controller']+1e-9
    return dict(null_dimension=len(d),radius=radius,lambda_kkt=float(lam),kkt_residual=float(kkt),objective_replay_error=float(abs(pred-w['net_load_less_controller'])),ledger=w,comparison_fixtures=20)


def fixtures():
    # Synthetic, dimensionless grid. Every active species and field component is in the return condition.
    g=Grid(.8,[cell(1.,(1.,),(.3,),(-.5,)),cell(1.2,(.8,),(.4,),(1.,),.5)],1.)
    h=.15; n=18; ports=np.zeros((g.size,6)); observe=np.zeros(g.size)
    for i,(sl,_,_) in enumerate(g.local): ports[sl.start:sl.start+3,3*i:3*i+3]=np.eye(3)
    observe[g.local[-1][0].start]=1.; L,B,p=lifted(g,h,n,ports,observe)
    # Same receiver observation and complete return, both with and without external input.
    target=np.zeros(g.size+1); target[-1]=.12
    t=np.arange(n)*h; source=np.column_stack([.4*np.sin(t),.3*np.cos(t)])
    output={}; rng=np.random.default_rng(369); rank=int(np.linalg.matrix_rank(B))
    for label,external in [('source_on',source),('source_off',source*0)]:
        rhs=target-L@external.ravel(); x=np.linalg.lstsq(B,rhs,rcond=1e-12)[0]; residual=np.linalg.norm(B@x-rhs); assert residual<1e-9
        z,ledger,_=run(g,h,p,external,ports,x.reshape(n,-1),observe)
        assert np.linalg.norm(z-target)<1e-9
        # Orthogonal nullspace perturbation preserves the endpoint but cannot lower the norm.
        d=rng.normal(size=B.shape[1]); d-=np.linalg.lstsq(B,B@d,rcond=1e-12)[0]; assert np.linalg.norm(B@d)<1e-9 and abs(x@d)<1e-8
        assert np.linalg.norm(x+d)>=np.linalg.norm(x)-1e-10
        # Distinct work ledger despite the same linear endpoint; source attribution is not an observer identity.
        other,second,_=run(g,h,p,external,ports,(x+d).reshape(n,-1),observe); assert np.linalg.norm(other-target)<1e-9
        assert abs(second['load']-ledger['load'])>1e-6
        if label=='source_off': assert ledger['net_load_less_controller']<=1e-10 and second['net_load_less_controller']<=1e-10
        opt=maximize_net(g,h,p,external,ports,observe,B,x,2.,rng)
        if label=='source_off': assert opt['ledger']['net_load_less_controller']<=1e-10
        output[label]=dict(optimized=opt,endpoint_residual=float(np.linalg.norm(z-target)),control_norm=float(np.linalg.norm(x)),null_perturbation_norm=float(np.linalg.norm(d)),ledger=ledger,same_endpoint_alternative_ledger=second)
    # A zero observed receiver output is not equivalent to a complete state return.
    H=B[-1:]; d=rng.normal(size=B.shape[1]); d-=np.linalg.lstsq(H,H@d,rcond=None)[0]
    assert abs(float((H@d)[0]))<1e-10 and np.linalg.norm(B[:-1]@d)>1e-3
    return dict(status='CONDITIONAL_FINITE_GRID_REVERSE_ENDPOINT',state_dimension=g.size,steps=n,control_coordinates=B.shape[1],endpoint_rank=rank,receiver_only_rank=int(np.linalg.matrix_rank(H)),cases=output,receiver_only_restoration_rejected=True,physical_admission=False,scope='Synthetic fixed-coefficient prescribed boundary experiment. Net work optimized over endpoint-null coordinates with explicit synthetic radius; not a physical controller constraint. Minimum Euclidean drive norm is not minimum signed controller work. Receiver linear observation is not useful energy. No actual source or receiver admission.')

if __name__=='__main__': print(json.dumps(fixtures(),indent=2))
