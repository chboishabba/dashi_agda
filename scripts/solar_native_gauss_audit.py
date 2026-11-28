"""Original shell signed constraint audit; global reference is nonlocal."""
import numpy as np
from scipy.linalg import null_space,solve
from solar_spherical_geometry import geometry
from solar_spherical_material_weld import construct,structural_stage_atlas
from solar_physical_cone import timed_step

def audit(dt=.001):
    radii=[1.,1.2];v,mesh,ne,nf=geometry(radii,0);n=len(v);z=np.zeros((n,3))
    m=construct(radii,0,np.arange(n),v,z,z,z,np.tile([0.,0.,1.],(n,1)))
    H=m['generator'];N=ne+nf;A=H[:N,:N];d0,d1,d2=m['incidence'];me,mb=m['energy_masses']
    Q=np.block([[d0.T*np.sqrt(me),np.zeros((d0.shape[1],nf))],[np.zeros((d2.shape[0],ne)),d2/np.sqrt(mb)]])
    Q=Q/np.linalg.norm(Q,axis=1)[:,None];K=null_space(Q);P=K@K.T
    _,r=timed_step(np.zeros(len(H)),H,np.zeros(len(H)),dt,mesh,atlas_pairs=structural_stage_atlas(m,mesh))
    T=np.eye(N)
    for e in r['events']:
        ix=np.array(e['coordinates']);
        if np.any(ix>=N):
            assert not np.any(H[np.ix_(ix,ix)]) if e['face_id'] is None else not H[ix[0],ix[1]]
            continue
        a=H[np.ix_(ix,ix)].copy()
        if e['face_id'] is not None:np.fill_diagonal(a,0)
        I=np.eye(len(ix));T[ix]=solve(I-dt*a/2,(I+dt*a/2)@T[ix])
    U=solve(np.eye(N)-dt*A/2,np.eye(N)+dt*A/2)
    D=(np.eye(N)-P)@T@K
    assert np.linalg.norm(Q@A)/np.linalg.norm(A)<1e-14
    assert np.linalg.norm(T.T@T-np.eye(N))<1e-10
    assert np.linalg.norm(D)>1e-3
    assert np.linalg.norm(Q@U-Q)<1e-8
    # Independent replay of actual scheduler on one physical vector.
    x=K[:,0];y,_=timed_step(np.r_[x,np.zeros(len(H)-N)],H,np.zeros(len(H)),dt,mesh,atlas_pairs=structural_stage_atlas(m,mesh))
    assert np.linalg.norm(y[:N]-T@x)<1e-12
    return dict(status='NATIVE_GAUSS_AUDIT_PASS',field_dimension=N,physical_dimension=K.shape[1],constraint_rank=N-K.shape[1],split_leakage_norm=float(np.linalg.norm(D,2)),split_constraint_norm=float(np.linalg.norm(Q@T-Q,2)),reference_constraint_norm=float(np.linalg.norm(Q@U-Q,2)),split_energy_defect=float(np.linalg.norm(T.T@T-np.eye(N))),physical_admission=False,causal_reference_admission=False)
if __name__=='__main__':print(audit())
