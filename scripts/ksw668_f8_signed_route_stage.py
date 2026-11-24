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
