"""Constraint-preserving vacuum cochain reference, explicit local star shears.
Staggered energy, not the original simultaneous physical energy or light cone.
"""
import numpy as np
from scipy.linalg import null_space
from solar_spherical_geometry import geometry
from solar_spherical_material_weld import construct

def step(C,e,b,h):
    # Each face receives its oriented boundary; each edge its dual coboundary.
    b1=b-h*(C@e)
    e1=e+h*(C.T@b1)
    return e1,b1

def audit():
    v,mesh,ne,nf=geometry([1.,1.2],0);n=len(v);z=np.zeros((n,3))
    m=construct([1.,1.2],0,np.arange(n),v,z,z,z,np.tile([0.,0.,1.],(n,1)))
    me,mb=m['energy_masses'];d0,d1,d2=m['incidence'];C=-m['generator'][ne:ne+nf,:ne]
    Qe=d0.T*np.sqrt(me);Qb=d2/np.sqrt(mb)
    Qe/=np.linalg.norm(Qe,axis=1)[:,None];Qb/=np.linalg.norm(Qb,axis=1)[:,None]
    assert np.linalg.norm(Qe@C.T)/np.linalg.norm(C)<1e-14
    assert np.linalg.norm(Qb@C)/np.linalg.norm(C)<1e-14
    # Frobenius bound guarantees h ||C|| <= 1/2, not just sampled spectrum.
    h=.5/np.linalg.norm(C);K=np.block([[np.eye(ne)-h*h*C.T@C,h*C.T],[-h*C,np.eye(nf)]])
    G=np.block([[np.eye(ne),-h*C.T/2],[-h*C/2,np.eye(nf)]])
    Q=np.block([[Qe,np.zeros((len(Qe),nf))],[np.zeros((len(Qb),ne)),Qb]])
    assert np.linalg.norm(Q@K-Q)<1e-12
    assert np.linalg.norm(K.T@G@K-G)<1e-12
    x=null_space(Q)[:,0];e,b=x[:ne],x[ne:];E0=x@G@x
    for _ in range(1000):e,b=step(C,e,b,h)
    y=np.r_[e,b];assert abs(y@G@y-E0)<1e-11 and np.linalg.norm(Q@y)<1e-11
    return dict(status='GAUSS_LEAPFROG_PASS',step_s=h,field_dimension=len(x),constraint_defect=float(np.linalg.norm(Q@K-Q)),modified_energy_defect=float(np.linalg.norm(K.T@G@K-G)),long_run_constraint=float(np.linalg.norm(Q@y)),long_run_energy_error=float(abs(y@G@y-E0)),simultaneous_energy_preserved=False,physical_causal_admission=False)
if __name__=='__main__':print(audit())
