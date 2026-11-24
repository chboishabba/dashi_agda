"""Same-route indexed receiver window, original jet bank, signed evolution faces."""
import json,os
from pathlib import Path
import numpy as np
from ksw668_f8_signed_route_stage import step
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver,forced_identity
from check_f8_h05_signed_receiver_cube import cube
from check_f8_p0_original_same_clock_state import cubic,signed_normal_fibre

def save_window(path,X,k,identity,window):
    p=Path(path);tmp=p.with_suffix(p.suffix+'.tmp')
    with tmp.open('wb') as f:
        np.savez(f,X=X,k=k,identity=json.dumps(identity,sort_keys=True),
                 **{'slot_'+str(i):x for i,x in window.items()})
        f.flush();os.fsync(f.fileno())
    os.replace(tmp,p)

def load_window(path,identity):
    with np.load(path,allow_pickle=False) as z:
        if z['identity'].item()!=json.dumps(identity,sort_keys=True):
            raise ValueError('receiver window identity mismatch')
        X=z['X'].copy();k=int(z['k']);nt=identity['nt']
        window={int(s[5:]):z[s].copy() for s in z.files if s.startswith('slot_')}
    expected=set(range(nt-1,min(k,nt+1)+1))
    if not 0<=k<=nt+1 or set(window)!=expected or not np.isfinite(X).all():
        raise ValueError('missing or invalid window slots')
    if any(x.shape!=X.shape or not np.isfinite(x).all() for x in window.values()):
        raise ValueError('invalid window arrays')
    if k in window and not np.array_equal(window[k],X):
        raise ValueError('latest state differs from indexed snapshot')
    return X,k,window

def intervene(X,v,c):
    Y=X.copy();Y[1]-=(1-v)*c;Y[2]+=(1+v)*c
    return Y

def receiver_report(window,nt,T0,dt,coeff,t,r,eps,dr,dy,src,cp,cm,route):
    X=np.stack([window[i] for i in (nt-1,nt,nt+1)])
    clocks=[T0+i*dt for i in (nt-1,nt,nt+1)]
    vel=np.array([coeff(T)[0] for T in clocks]);amp=coeff(clocks[1])[2]
    ny,nr=X.shape[-2:]
    # receiver_bank indexes even entries in a local half-step array.
    bank_vel=np.zeros(5);bank_vel[::2]=vel
    obs=receiver_bank(t,r,eps,dr,dy,dt,bank_vel,1,nr,ny)
    g=radial_source_at_receiver(src,amp,r,eps,dr)
    faces,paths,values=cube(X,vel,obs,g)
    original=values[str((0,0,0))]
    err,scale=forced_identity(original,g,t)
    if not np.all(abs(err)<=1e-10*np.maximum(1.,scale)):
        raise ValueError('original off-shell Weyl identity failed')
    ids,w=cubic(r,dr,nr)
    def read(f):
        return [(r/eps)**ell*float(w@f[q,ids]) for q,ell in enumerate((0,2,4))]
    U,P,M=X[1,:3]
    W,N,Q,G,I,K,_=signed_normal_fibre(U,P,M,dy,vel[1],amp*src)
    # Actual time naturality residual for each frozen-history intervention:
    # advance intervention of input versus intervention of advanced output.
    # Histories stay fixed as labels at each vertex, not reinterpreted as
    # histories of the perturbed solution.
    defects={}
    for i in range(2):
        baseline=step(X[i],clocks[i],dt,coeff,dr,dy,src,cp,cm,route)
        np.testing.assert_allclose(baseline,X[i+1],rtol=1e-10,atol=1e-12)
        for a,name in enumerate(('R','J','K')):
            left=step(intervene(X[i],vel[i],X[i,3+a]),clocks[i],dt,coeff,dr,dy,src,cp,cm,route)
            right=intervene(X[i+1],vel[i+1],X[i+1,3+a])
            d=left[:3]-right[:3]
            dw=((1+vel[i+1])*d[1]+(1-vel[i+1])*d[2])/2
            dn=(d[1]-d[2])/2
            defects[str(i)+name]=dict(max_abs=float(np.max(abs(d))),
                mode_U=read(d[0,:,0,:]),mode_W=read(dw[:,0,:]),mode_N=read(dn[:,0,:]))
    return dict(r=r,clock_indices=[nt-1,nt,nt+1],bulk_clocks=clocks,
                mode_H=read(U[:,0,:]),mode_Q=read(Q[:,0,:]),mode_G=read(G),
                mode_I=read(I),mode_N=read(N[:,0,:]),
                rows=['E4','legacy4','direct','SMS','geometric_F_minus_source','bulk_residual'],
                mode_observers=original.tolist(),source_offset=g.tolist(),
                fixed_history_faces=faces,reversible_paths=paths,
                evolution_faces=defects,physical_commutation_proved=False)
