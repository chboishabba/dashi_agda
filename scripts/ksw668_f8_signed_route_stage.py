"""Opt-in F8 weighted4 paired correction / signed ledger; original stage unchanged."""
import numpy as np

def defect(f,b,h,adjoint=False):
    # Arrays (multipole, normal, radial); O(n) stencil, weighted adjoint by scatter.
    z=b+h*np.arange(f.shape[1])
    H=np.ones(len(z)); H[[0,-1]]=0.5
    B=H*z**-3
    out=1.5*f/z[None,:,None]
    for i in range(len(z)):
        neighbors=[(1,1.)] if i==0 else ([(i-1,-1.)] if i==len(z)-1 else [(i-1,-.5),(i+1,.5)])
        for j,d in neighbors:
            c=d*np.expm1(-1.5*np.log1p((z[j]-z[i])/z[i]))/h
            if adjoint: out[:,j,:]+=c*B[i]/B[j]*f[:,i,:]
            else: out[:,i,:]+=c*f[:,j,:]
    return out

def rhs(X,dr,dy,b,v,amp,src,cp,cm,route):
    from ksw668_f8_weighted_normal_stage import weighted_stage4
    if route not in ('paired','ledger'): raise ValueError('explicit route required')
    U,P,M=X[:3]; out=np.zeros_like(X)
    weighted_stage4(U,P,M,*out[:3],dr,dy,b,v,amp,src,cp,cm,4)
    W=((1+v)*P+(1-v)*M)/2; N=(P-M)/2
    cw=defect(W,b,dy)
    if route=='paired':
        dw=(1-v*v)*defect(N,b,dy,True); dn=-cw
        out[1]+=dw+(1-v)*dn
        out[2]+=dw-(1+v)*dn
    else: out[3]=cw
    I=((1+v)*P[:,0,:]+(v-1)*M[:,0,:])/2-amp*src
    out[4,:,0,:]=-2*I/dy
    out[5,:,-1,:]=-(1+v)*P[:,-1,:]/dy
    out[:,:,:,-1]=0
    return out

def step(X,T,dt,coeff,dr,dy,src,cp,cm,route):
    """Six channels U,P,M,R,wall history,top history; all at same stage clock."""
    def f(x,t):
        v,b,amp=coeff(t)
        return rhs(x,dr,dy,b,v,amp,src,cp,cm,route)
    a=X+dt*f(X,T)
    b=.75*X+.25*(a+dt*f(a,T+dt))
    return (X+2*(b+dt*f(b,T+dt/2)))/3

def save(path,X,k,identity):
    import os,json
    from pathlib import Path
    p=Path(path); tmp=p.with_suffix(p.suffix+'.tmp')
    with tmp.open('wb') as f:
        np.savez(f,X=X,k=k,identity=json.dumps(identity,sort_keys=True))
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp,p)

def load(path,identity):
    import json
    with np.load(path,allow_pickle=False) as z:
        if z['identity'].item()!=json.dumps(identity,sort_keys=True): raise ValueError('checkpoint identity mismatch')
        X=z['X'].copy(); k=int(z['k'])
    if X.ndim!=4 or X.shape[:2]!=(6,3) or k<0 or not np.isfinite(X).all(): raise ValueError('invalid checkpoint')
    return X,k


def rhs_transpose(Y,dr,dy,b,v,route):
    """Euclidean VJP of the homogeneous six-channel RHS on active radial nodes.
    Uses the original weighted4 transpose; affine prescribed source has zero VJP.
    """
    from warp_stage_adjoint import transpose
    if route not in ('paired','ledger'): raise ValueError('explicit route required')
    Y=Y.copy();Y[..., -1]=0
    out=np.zeros_like(Y)
    out[:3]=transpose(Y[:3],dr,dy,b,v,4)
    a,c=(1+v)/2,(1-v)/2
    z=b+dy*np.arange(Y.shape[-2])
    B=z**-3;B[[0,-1]]*=.5;B=B[None,:,None]
    # C^T=B C^dagger B^-1 and (C^dagger)^T=B C B^-1.
    def CT(x):return B*defect(x/B,b,dy,True)
    def CdT(x):return B*defect(x/B,b,dy)
    if route=='paired':
        p=Y[1]+Y[2]
        q=(1-v)*Y[1]-(1+v)*Y[2]
        w=-CT(q)
        n=(1-v*v)*CdT(p)
    else:
        w=CT(Y[3]);n=np.zeros_like(w)
    out[1]+=a*w+n/2
    out[2]+=c*w-n/2
    out[1,:,0,:]-=(1+v)*Y[4,:,0,:]/dy
    out[2,:,0,:]+=(1-v)*Y[4,:,0,:]/dy
    out[1,:,-1,:]-=(1+v)*Y[5,:,-1,:]/dy
    out[..., -1]=0
    return out

def reverse_step(Y,T,dt,coeff,dr,dy,route):
    """Transpose of actual Shu-Osher step with original stage clocks."""
    def BT(y,t):
        v,b,_=coeff(t)
        return y+dt*rhs_transpose(y,dr,dy,b,v,route)
    l2=2*BT(Y,T+dt/2)/3
    l1=BT(l2,T+dt)/4
    return Y/3+3*l2/4+BT(l1,T)

def receiver_defect_ledger(observations,errors,defects,T0,dt,coeff,dr,dy,route):
    """Signed endpoint identity for e[n+1]=E[n] e[n]+d[n].
    All arrays on the same fine carrier; observation/source offsets external.
    Return per-mode signed terms, never aggregate multipoles before checking.
    """
    if len(errors)!=len(observations) or len(defects)+1!=len(errors):
        raise ValueError('inconsistent indexed ledger')
    def contract(a,b):return np.sum(a*b,axis=(0,2,3))
    lam=observations[-1].copy();terms=[]
    for n in range(len(defects)-1,-1,-1):
        terms.append(contract(lam,defects[n]))
        lam=observations[n]+reverse_step(lam,T0+n*dt,dt,coeff,dr,dy,route)
    terms=np.asarray(terms[::-1])
    initial=contract(lam,errors[0])
    actual=sum(contract(o,e) for o,e in zip(observations,errors))
    predicted=initial+terms.sum(axis=0)
    bound=abs(initial)+abs(terms).sum(axis=0)
    if not np.all(np.isfinite([actual,predicted,bound])) or not np.all(abs(actual-predicted)<=1e-9*np.maximum(1.,bound)):
        raise ValueError('signed endpoint closure failed')
    return dict(actual=actual,initial=initial,terms=terms,predicted=predicted,absolute_bound=bound)
