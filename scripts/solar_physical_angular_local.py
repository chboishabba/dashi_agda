"""Local angular/radial shell transport; l=1 coefficients are observations.
No globally shared spherical-harmonic state is used as a causal coordinate.
The mesh is an independently supplied angular quadrature/adjacency. The
radial donor is reused separately for each patch, with local tangent ports.
Angular edge conductances are supplied physical curl coefficients, not inferred
from quadrature weights. This is a finite conditional model, not a converged
full spherical Maxwell discretization.
"""
import numpy as np
from solar_physical_radial_ladder import build
from solar_periodic_radial_weld import R,H
from scipy.constants import epsilon_0

def local_shell(cfg):
    n=len(cfg['volumes_m3']); k=int(cfg['radial_cells'])
    normals=np.asarray(cfg['normals'],float); areas=np.asarray(cfg['areas_m2'],float)
    frames=np.asarray(cfg['ned_to_cartesian'],float)
    assert normals.shape==(n,3) and np.allclose(np.linalg.norm(normals,axis=1),1)
    assert areas.shape==(n,) and np.all(areas>0)
    assert np.allclose(frames@frames.transpose(0,2,1),np.eye(3)) and np.allclose(np.linalg.det(frames),1)
    # Each patch has two tangential polarizations; retain a TE and TM ladder
    # for each. This patch chart is not a literal restriction of global l=1.
    donor,radii=build(k,cfg['shell_sigma_S_m'],cfg['ground_admittance_normalized'])
    modes=[0,1,3,4]; ix=np.concatenate([np.arange(3*k*m,3*k*(m+1)) for m in modes])
    J0=np.asarray(donor['J_s_inv'])[np.ix_(ix,ix)]
    Rg0=np.asarray(donor['R_ground_s_inv'])[np.ix_(ix,ix)]
    Ro0=np.asarray(donor['R_other_s_inv'])[np.ix_(ix,ix)]
    B0=np.asarray(donor['B'])[np.ix_(ix,modes)]
    m=len(ix); p=4*n
    J=np.kron(np.eye(n),J0); Rg=np.kron(np.eye(n),Rg0); Ro=np.kron(np.eye(n),Ro0); B=np.kron(np.eye(n),B0)
    # Independent angular coupling: each edge acts on a pair of actual local
    # coordinates at the same radial cell. Skew ownership ensures no energy gain.
    angular=cfg.get('angular_edges',[]); seen=set()
    for edge in angular:
        a,b,j,u,v,rate=[edge[z] for z in ('source','target','radial_cell','source_slot','target_slot','rate_s_inv')]
        assert 0<=a<n and 0<=b<n and a!=b and 0<=j<k and 0<=u<12 and 0<=v<12 and np.isfinite(rate)
        i=a*m+3*k*(u//3)+3*j+u%3; h=b*m+3*k*(v//3)+3*j+v%3
        key=tuple(sorted((i,h))); assert key not in seen; seen.add(key)
        J[i,h]+=rate; J[h,i]-=rate
    d=len(cfg['curl_s_inv']); C=np.zeros((p,d))
    for a in range(n):
        # Local tangent frame, independent of harmonic basis. Split the
        # two tangent components equally into the two selected branch charts.
        t=np.asarray(cfg['tangent_frames'][a],float)
        assert t.shape==(2,3) and np.allclose(t@t.T,np.eye(2)) and np.allclose(t@normals[a],0)
        vol=cfg['volumes_m3'][a]; assert vol>0
        C[4*a:4*a+4,12*a:12*a+3]=np.tile(t@frames[a],(2,1))*np.sqrt(areas[a]/(2*epsilon_0*vol))
    spec=dict(J_s_inv=J.tolist(),B=B.tolist(),R_ground_s_inv=Rg.tolist(),R_other_s_inv=Ro.tolist(),
              D_ground_S=np.zeros((p,p)).tolist(),D_other_S=np.zeros((p,p)).tolist())
    # Do not manufacture physical mesh adjacency: check supplied shell
    # coordinate positions against the radial locations and original patch IDs.
    mesh=cfg['indexed_mesh']; pos=np.asarray(mesh['positions_m'],float)
    site=np.asarray(mesh['coordinate_site'],int); assert site.shape==(d+n*m,)
    for a in range(n):
        assert np.all(site[12*a:12*a+12]==site[12*a])
        for mode in range(4):
            for j,r in enumerate(radii):
                ids=site[d+a*m+3*k*mode+3*j:d+a*m+3*k*mode+3*j+3]
                assert np.allclose(pos[ids],r*normals[a],rtol=0,atol=1e-6)
    return spec,C

def observe_dipole(tangent, normals, areas):
    """Weighted projection + exact complement of local Cartesian tangent data.
    No feedback through this nonlocal observation.
    """
    x=np.asarray(tangent,float); n=np.asarray(normals,float); w=np.asarray(areas,float)
    assert x.shape[-2:]==n.shape and n.shape[1]==3 and np.all(w>0)
    w=w/w.sum()
    assert np.allclose(np.einsum('...ij,ij->...i',x,n),0)
    A=np.array([np.sqrt(1.5)*np.column_stack((np.cross(q,np.eye(3)).T,np.eye(3)-np.outer(q,q))) for q in n])
    B=A.reshape(-1,6); weights=np.repeat(np.sqrt(w),3)
    W=B*weights[:,None]; y=x.reshape(*x.shape[:-2],-1)*weights
    inv=np.linalg.pinv(W); coeff=y@inv.T
    complement=y-coeff@W.T
    assert np.allclose(complement@W,0,atol=1e-10*max(1.,np.linalg.norm(y)))
    assert np.allclose(coeff@W.T+complement,y)
    return dict(coefficients=coeff,weighted_complement=complement,rank=int(np.linalg.matrix_rank(W)),
                reconstruction=(coeff@W.T+complement).reshape(x.shape)/np.sqrt(w)[:,None])
