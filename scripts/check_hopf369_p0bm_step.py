"""BM: tube-preserving nonlinear update in the existing BK projected basis.
Held-out diagnostics, not an existence or continuum residual certificate.
"""
from check_hopf369_p0bk_projection import *
from check_hopf369_p0bl_fit import bound
from fractions import Fraction as F

def map_projection():
    return np.stack([projected_coefficients(v) for v in np.eye(252)],axis=1)

def projected_design(X,V,P):
    # Build two scalar-jet product maps by column.  Vectorized over all basis functions.
    r=np.sum(X[:,:3]**2,axis=1);x=X[:,:3];v=1-r*r
    d=np.zeros((len(X),4));d[:,:3]=-4*r[:,None]*x
    dd=np.zeros((len(X),4,4));dd[:,:3,:3]=-4*r[:,None,None]*np.eye(3)-8*x[:,:,None]*x[:,None,:]
    def prod(V,v,d,dd):
        out=V*v[:,None,None]
        out[:,1:5]+=d[:,:,None]*V[:,:1]
        out[:,5:]+=(dd[:,:,:,None]*V[:,0,None,None,:]+d[:,:,None,None]*V[:,None,1:5,:]+d[:,None,:,None]*V[:,1:5,None,:]).reshape(len(X),16,-1)
        return out
    blend=V@P+prod(V-V@P,v,d,dd)
    return prod(blend,v,d,dd)

def run(c,cs):
    eps=.025; P=map_projection(); assert np.max(abs(P@c-cs))<1e-12
    def ends(seed,power):
        x=sample(power,seed)[:,:3];return np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]])
    X=sample(10,123); Y=sample(10,456); S=ends(789,6); Z=ends(987,7)
    # Center computed using pinned coefficients, not recalculated projection.
    def prepare_trial(X):
        B,V=prepare(X,eps,4,2);q=trial(X,V@c,V@cs,2);D=projected_design(X,V,P)
        psi=weight52(X,np.asarray(Wfun(j.array(X),eps)))[:,0]
        return B,q,D,psi
    B,q,V,p=prepare_trial(X);S0,s,U,ps=prepare_trial(S);T,t,W,pt=prepare_trial(Y);Q,z,H,pz=prepare_trial(Z)
    residual=lambda B,q,p:np.asarray(Rbatch(*B,q))/p
    jac=lambda B,q,V,p:np.einsum('ni,nij->nj',np.asarray(DJ(*B,q)),V)/p[:,None]
    f=residual(B,q,p);g=residual(S0,s,ps);A=jac(B,q,V,p);E=jac(S0,s,U,ps)
    rows=np.vstack([A,E]);rhs=-np.r_[f,g];scale=np.maximum(np.linalg.norm(rows,axis=0),1e-12);rows=rows/scale
    # Ridge is applied after column normalization, to suppress basis cancellation.
    def rms(x):return float(np.sqrt(np.mean(x*x)))
    base=np.array([rms(residual(T,t,pt)),rms(residual(Q,z,pz))]);print('base weighted test bulk,seam RMS',base,'max',np.max(abs(residual(T,t,pt))),np.max(abs(residual(Q,z,pz))),flush=True)
    best=None; caps=np.array([398e-6,2749e-6,2325e-6])
    for ridge in (.02,.1,.5):
        d=lstsq(np.vstack([rows,ridge*np.eye(252)]),np.r_[rhs,np.zeros(252)],cond=1e-12,lapack_driver='gelsy')[0]/scale
        ds=P@d
        # Full-domain interval upper bounds for correction. Coarser enclosure is
        # still rigorous, and the final accepted direction is replayed at BL resolution.
        bounds=np.array(bound(d,ds,128,128));r=max(bounds/caps)
        a=2.**min(0,int(np.floor(np.log2(.98/r)))) if r>0 else 1.
        out=np.array([rms(residual(T,t+a*(W@d),pt)),rms(residual(Q,z+a*(H@d),pz))]);score=np.linalg.norm(out)
        print('ridge',ridge,'step',a,'bounds',bounds*a,'test bulk,seam',out,'score',score,flush=True)
        if best is None or score<best[0]:best=(score,d,ds,a,ridge)
    _,d,ds,a,ridge=best;d=d*a;ds=ds*a
    bnd=bound(d,ds,512,256)
    # Binary64 endpoints are compared to exact rational caps; scaling by 2 is exact.
    while not all(F(float(x))<F(float(y)) for x,y in zip(bnd,caps)):
        d=d/2;ds=ds/2;a=a/2;bnd=bound(d,ds,512,256)
    tr=residual(B,q+V@d,p);trseam=residual(S0,s+U@d,ps)
    u=residual(T,t+W@d,pt);v=residual(Q,z+H@d,pz)
    print('accepted ridge/step',ridge,a,'certified correction bounds',bnd,'training weighted RMS',rms(tr),rms(trseam),'held-out weighted RMS',rms(u),rms(v),'held-out weighted max',np.max(abs(u)),np.max(abs(v)),flush=True)
    print('held-out unweighted RMS/max',rms(u*pt),np.max(abs(u*pt)),rms(v*pz),np.max(abs(v*pz)),flush=True)
    assert np.linalg.norm([rms(u),rms(v)])<np.linalg.norm(base)
    # Independent junction diagnostics, actual candidate. Projection shape and first seam algebra are exact.
    a0=seam(Q,z+H@d,len(Z)//2);print('held-out normalized first/TF/scalar',a0,flush=True);assert max(a0[:2])<1e-8
    # Reuse BK sign transport for both pinned base and correction.
    def reflect(c):
        out=c.copy();out[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;out[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();return out
    V0=Y[:128];B0,Va=prepare(V0,eps,4,2);q0=trial(V0,Va@c,Va@cs,2)+trial(V0,Va@d,Va@ds,2)
    R=V0.copy();R[:,3]=L-R[:,3];Bn,Vn=prepare(R,-eps,4,2);qn=trial(R,Vn@reflect(c),Vn@reflect(cs),2)+trial(R,Vn@reflect(d),Vn@reflect(ds),2)
    Bz,Vz=prepare(V0,0.,4,2);a1=np.max(abs(np.asarray(Rbatch(*B0,q0))-np.asarray(Rbatch(*Bn,qn))));a2=np.max(abs(np.asarray(Rbatch(*Bz,np.zeros_like(q0)))));print('signed/zero max',a1,a2,flush=True);assert max(a1,a2)<1e-8
    out={'correction':d.tolist(),'projected_correction':ds.tolist(),'ridge':ridge,'step':a,'bounds':bnd,'weighted_test_rms':[rms(u),rms(v)]}
    Path('bm_step.json').write_text(json.dumps(out,separators=(',',':'))+'\n')

if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));cs=np.array(json.loads(Path(sys.argv[2]).read_text()));assert len(c)==len(cs)==252
    run(c,cs)
