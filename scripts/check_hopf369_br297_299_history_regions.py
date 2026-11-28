"""Independent temporal jets and spatially resolved constraint diagnostics.
Replay BR296, retain all defects; no constraint projection or continuum claim.
"""
import argparse
import inspect
import numpy as np
from scipy.interpolate import RegularGridInterpolator
import check_hopf369_br296_cmc_history as history
import check_hopf369_br287_289_g4_audit as audit

def capture(n,steps,dt):
    records=[]
    d=audit.d
    def save(g,v,U,dx):
        records.append((g.copy(),v.copy(),U.copy(),dx))
    source=inspect.getsource(d.run)
    assert '    b0=divB(U);' in source and 'margin=min(margin,m,mm);' in source
    source=source.replace('    b0=divB(U);','    save(g,v,U,dx)\n    b0=divB(U);').replace('margin=min(margin,m,mm);','save(g,v,U,dx);margin=min(margin,m,mm);')
    def replay(nn,ss,dd):
        ns=dict(vars(d),save=save)
        exec(source,ns)
        ns['run'](nn,ss,dd)
    old=audit.run
    try:
        audit.run=replay
        history.run(n,steps,dt)
    finally:
        audit.run=old
    assert len(records)==steps+1
    return records

def evaluate(record,acc,coordinate_velocity=None):
    g,v,U,dx=record
    d=audit.d
    T,_,_,_,_=d.matter(g,U)
    I=np.linalg.inv(g)
    v=v if coordinate_velocity is None else coordinate_velocity
    first=np.stack([v,*[audit.diff(g,i,dx) for i in range(3)]],axis=-3)
    second=np.zeros(g.shape[:-2]+(4,4,4,4))
    second[...,0,0,:,:]=acc
    for i in range(3):
        second[...,0,i+1,:,:]=second[...,i+1,0,:,:]=audit.diff(v,i,dx)
        second[...,i+1,i+1,:,:]=(np.roll(g,-1,axis=i)-2*g+np.roll(g,1,axis=i))/dx**2
        for j in range(i):
            second[...,i+1,j+1,:,:]=second[...,j+1,i+1,:,:]=audit.diff(audit.diff(g,i,dx),j,dx)
    out=np.full(g.shape[:3]+(4,),np.nan)
    for q in np.ndindex(tuple(s-2 for s in g.shape[:3])):
        p=tuple(i+1 for i in q)
        R,C,DC=audit.curvature(g[p],first[p],second[p])
        tr=np.sum(I[p]*R)
        E=R-.5*g[p]*tr-d.src.KAP*T[p]
        normal=-I[p][:,0]/np.sqrt(-I[p][0,0])
        S=d.src.KAP*(T[p]-.5*g[p]*np.sum(I[p]*T[p]))
        reduced=R-(DC+DC.T)/2-S
        out[p]=[abs(2*normal@E@normal),np.max(abs(normal@E[:,1:])),np.max(abs(C)),np.max(abs(reduced))]
    return out

def run(n,steps,dt):
    assert n>=6 and steps>=2
    records=capture(n,steps,dt)
    k=steps//2
    g,v,U,dx=records[k]
    gm,vm,_,_=records[k-1]
    gp,vp,_,_=records[k+1]
    # Entirely history-derived temporal jets, independent of the RHS.
    v_fd=(gp-gm)/(2*dt)
    a_fd=(gp-2*g+gm)/dt**2
    a_v=(vp-vm)/(2*dt)
    T,_,_,_,_=audit.d.matter(g,U)
    I=np.linalg.inv(g)
    tr=np.sum(I*T,axis=(-2,-1))
    a_rhs=audit.d.acc(g,v,dx)-2*audit.d.src.KAP*(T-.5*g*tr[...,None,None])/I[...,0,0,None,None]
    fields=[evaluate(records[k],a_rhs),evaluate(records[k],a_fd,v_fd),evaluate(records[k],a_v)]
    idx=np.indices((n,)*3)
    distance=np.min(np.minimum(idx,n-1-idx),axis=0)
    for tag,field in zip(('matched','metric-history','velocity-history'),fields):
        for band,mask in [('outer-band',distance==1),('core',distance>=2)]:
            vals=field[mask]
            assert np.all(np.isfinite(vals))
            print('BR297',n,steps,dt,tag,band,'H M C reduced',np.max(vals,axis=0).tolist(),flush=True)
    core=distance>=2
    print('BR298 temporal discrepancies',np.max(abs(v_fd-v)[core]),np.max(abs(a_fd-a_rhs)[core]),np.max(abs(a_v-a_rhs)[core]),flush=True)
    # All grids n>=6 contain [-.3,.3]^3 in their two-cell core.
    # Interpolate residual magnitudes, not claim an exact common-coordinate jet.
    grid=np.linspace(-1.5,1.5,n)[1:-1]
    x=np.array([-.3,0.,.3])
    points=np.stack(np.meshgrid(x,x,x,indexing='ij'),axis=-1)
    vals=RegularGridInterpolator((grid,)*3,fields[1][1:-1,1:-1,1:-1],bounds_error=True)(points)
    assert np.all(np.isfinite(vals))
    print('BR299 common coordinate interpolated diagnostic magnitudes',np.max(vals,axis=(0,1,2)).tolist(),flush=True)
    # Matched contraction should close on the core; independent temporal defects
    # are deliberately not asserted zero.
    assert np.max(fields[0][core,3])<1e-9

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--n',type=int,default=6)
    p.add_argument('--steps',type=int,default=4)
    p.add_argument('--dt',type=float,default=.001)
    a=p.parse_args()
    run(a.n,a.steps,a.dt)
