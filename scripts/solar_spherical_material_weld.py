"""Local positive diagonal Hodge approximation on the same Whitney complex.
Retains consistent mass as reference; no claim of continuum convergence.
Material coupling uses actual Whitney edge integrals of piecewise constant J.
"""
import numpy as np
from itertools import combinations
from scipy.constants import epsilon_0
from solar_spherical_whitney import shell_mesh,whitney,normalized
from solar_metric_cochain_weld import metric_curl
from solar_physical_cone import timed_step

from functools import lru_cache
from scipy.sparse import csr_matrix,bmat,diags,block_diag,issparse,triu
from solar_matrix_storage import close

@lru_cache(maxsize=4)
def assembly_mesh(radii,level,nested_depth=0):
    """Original projected shell, optionally one exact nested subdivision.
    Nested depth is independent of projected angular level.
    """
    if nested_depth not in (0,1):raise ValueError('one nested depth supported')
    xyz,s,m,d=shell_mesh(radii,level)
    if nested_depth:
        from solar_nested_cochain_refinement import nested_cochains
        bundle=nested_cochains(xyz,s);xyz,s=bundle['xyz'],bundle['simplices']
        m=[{t:i for i,t in enumerate(row)} for row in s]
        d=[a.toarray() for a in bundle['fine_incidence']]
    return xyz,s,m,d

@lru_cache(maxsize=12)
def _prepared_static_geometry(radii,level,cell_owner,volumes,nested_depth=0):
    """Invariant signed cochain and reciprocal Whitney map, one per mesh."""
    xyz,s,m,d=assembly_mesh(radii,level,nested_depth)
    E,B,V=whitney(xyz,s,m)
    # Positive diagonal scaling, not row sums (signed bases).
    me=np.diag(E).copy(); mb=np.diag(B).copy()
    K=metric_curl(*d,me,mb)
    ne=len(me); nf=len(mb); owners=np.asarray(cell_owner,int)
    vol=np.asarray(volumes,float); n=len(vol)
    assert owners.shape==(len(s[3]),) and np.all((owners>=0)&(owners<n))
    assert np.all(vol>0)
    W=np.zeros((ne,3*n)); actual=np.zeros(n)
    for tet,o in zip(s[3],owners):
        p=xyz[list(tet)]; v=abs(np.linalg.det((p[1:]-p[0]).T))/6
        scale=np.max(np.linalg.norm(p-p[0],axis=1))
        g=np.linalg.inv(np.column_stack((np.ones(4),(p-p[0])/scale)))[1:,:].T/scale
        actual[o]+=v
        for i,j in combinations(range(4),2):
            W[m[1][(tet[i],tet[j])],3*o:3*o+3]+=v*(g[j]-g[i])/4
    assert np.allclose(actual,vol,rtol=1e-9,atol=0)
    # Exact metric discrepancy on the identical unnormalized cochains.
    ref,LE,LB=normalized(d,E,B)
    T=np.block([[LE.T/np.sqrt(me)[None,:],np.zeros((ne,nf))],
                [np.zeros((nf,ne)),LB.T/np.sqrt(mb)[None,:]]])
    defect=T@K-ref@T
    return (K,me,mb,W,ref,T,defect,d,xyz,s,owners,vol,E,B)

def construct(radii,level,cell_owner,volumes,Dspecies,nu,gyro,axis,nested_depth=0,sparse_operator=False):
    K,me,mb,W,ref,T,defect,d,xyz,s,owners,vol,E,B=_prepared_static_geometry(
        tuple(float(v) for v in radii),int(level),
        tuple(int(v) for v in cell_owner),tuple(float(v) for v in volumes),int(nested_depth))
    ne=len(me); nf=len(mb); n=len(vol)
    # xJ = sqrt(V/D) J; reciprocal force uses identical integrated basis.
    Ds=np.asarray(Dspecies,float); nu=np.asarray(nu,float); gyro=np.asarray(gyro,float); axis=np.asarray(axis,float)
    assert Ds.shape==nu.shape==gyro.shape==(n,3) and np.all(Ds>=0) and np.all(nu>=0)
    assert axis.shape==(n,3) and np.allclose(np.linalg.norm(axis,axis=1),1)
    size=ne+nf+9*n
    sparse_operator=bool(sparse_operator or nested_depth)
    if sparse_operator:
        from scipy.sparse import lil_matrix
        A=lil_matrix((size,size));A[:ne+nf,:ne+nf]=csr_matrix(K)
    else:
        A=np.zeros((size,size));A[:ne+nf,:ne+nf]=K
    loss=np.zeros(size)
    for o in range(n):
        b=axis[o]; cross=np.array([[0,-b[2],b[1]],[b[2],0,-b[0]],[-b[1],b[0],0]])
        for j in range(3):
            sl=slice(ne+nf+9*o+3*j,ne+nf+9*o+3*j+3)
            coupling=W[:,3*o:3*o+3]*np.sqrt(Ds[o,j]/vol[o])/np.sqrt(me)[:,None]
            A[:ne,sl]=-coupling; A[sl,:ne]=coupling.T
            A[sl,sl]=-gyro[o,j]*cross if Ds[o,j]>0 else 0
            loss[sl]=nu[o,j] if Ds[o,j]>0 else 0
    if sparse_operator:A=A.tocsr();A.eliminate_zeros()
    assert close(A,-A.T,rtol=0,atol=0)
    R=diags(loss,format='csr') if sparse_operator else np.diag(loss)
    return dict(generator=A-R,exchange=A,loss=R,reference=ref,
                metric_transport=T,metric_defect=defect,incidence=d,positions=xyz,
                simplices=s,owners=owners,material_map=W,energy_masses=(me,mb),
                consistent_masses=(E,B),physical_admission=False)

def structural_stage_atlas(model,mesh):
    """Exact nonzero coordinate support of the fixed Whitney maps, independent of D.

    All species use the same geometric edge-current map. Zero exchange slots
    reserve time on their original indexed face, not on an invented connection.
    """
    W=np.asarray(model['material_map'])
    ne,n3=W.shape; n=n3//3
    N=model['generator'].shape[0]; nf=N-ne-9*n
    if n3!=3*n or nf<0:
        raise ValueError('invalid Whitney material chart')
    site=np.asarray(mesh['coordinate_site'])
    if site.shape!=(N,): raise ValueError('invalid atlas site map')
    pairs=set()
    E=model['exchange'][:ne+nf,:ne+nf]
    upper=triu(E,k=1) if issparse(E) else np.triu(E,1)
    for i,j in zip(*upper.nonzero()):
        if site[i]!=site[j]: pairs.add((int(i),int(j)))
    for e,k in zip(*np.nonzero(W)):
        o,component=divmod(int(k),3)
        for species in range(3):
            j=ne+nf+9*o+3*species+component
            if site[e]!=site[j]: pairs.add((int(e),j))
    return tuple(sorted(pairs))

def observe(model,P,L,x):
    from solar_metric_cochain_weld import observation,recover
    A=model['generator']; reduced,defect,Q=observation(A,P,L)
    y,r=recover(x,P,L)
    assert np.allclose(P@A@x,reduced@y+P@A@r)
    return dict(coarse=y,residual=r,operator_defect=defect,reduced=reduced)

def propagate(model,x,force,dt,mesh):
    # Caller supplies actual cochain/material site membership and face IDs.
    # The timed guard rejects unsupported nonlocal couplings.
    return timed_step(x,model['generator'],force,dt,mesh,{'collision':model['loss']})

def fixtures():
    radii=[1.,1.2]; xyz,s,m,d=shell_mesh(radii,0)
    v=sum(abs(np.linalg.det((xyz[list(t)][1:]-xyz[t[0]]).T))/6 for t in s[3])
    model=construct(radii,0,np.zeros(len(s[3]),int),[v],[[1.,0.,2.]],[[1.,0.,2.]],[[1.,0.,-1.]],[[0.,0.,1.]])
    A=model['generator']; x=np.random.default_rng(369).normal(size=len(A))
    assert np.isclose(x@A@x,-x@model['loss']@x,rtol=1e-6,atol=1e-6)
    P=np.eye(len(A))[:3]; obs=observe(model,P,P.T,x)
    assert np.allclose(P.T@obs['coarse']+obs['residual'],x)
    return dict(states=len(A),metric_defect_norm=float(np.linalg.norm(model['metric_defect'])),
                material_reciprocity=True,reconstruction=True,physical_admission=False)
if __name__=='__main__':
    import json
    print(json.dumps(fixtures(),indent=2))
