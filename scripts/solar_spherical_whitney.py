"""Piecewise-flat spherical shell Whitney cochain construction.
Octahedral angular triangulation, radial prism tetrahedralization, exact signed
incidence, Whitney mass matrices integrated by degree-two simplex quadrature.
No spherical continuum convergence or physical light-front admission asserted.
"""
import numpy as np
from itertools import combinations
from scipy.linalg import cholesky, solve_triangular
from scipy.constants import epsilon_0,mu_0

def shell_mesh(radii,levels=0):
    radii=np.asarray(radii,float)
    assert len(radii)>=2 and np.all(radii>0) and np.all(np.diff(radii)>0)
    assert isinstance(levels,int) and 0<=levels<=3
    v=[np.eye(3)[i]*s for i in range(3) for s in (-1,1)]
    tri=[(i,j,k) for i in (0,1) for j in (2,3) for k in (4,5)]
    for _ in range(levels):
        midpoint={}; new=[]
        def mid(a,b):
            key=tuple(sorted((a,b)))
            if key not in midpoint:
                p=v[a]+v[b]; midpoint[key]=len(v); v.append(p/np.linalg.norm(p))
            return midpoint[key]
        for a,b,c in tri:
            x,y,z=mid(a,b),mid(b,c),mid(c,a)
            new.extend([(a,x,z),(x,b,y),(z,y,c),(x,y,z)])
        tri=new
    n=len(v); xyz=np.concatenate([r*np.array(v) for r in radii])
    tetra=[]
    for layer in range(len(radii)-1):
        for face in tri:
            a,b,c=sorted(face); a+=layer*n;b+=layer*n;c+=layer*n
            tetra.extend([(a,b,c,c+n),(a,b,b+n,c+n),(a,a+n,b+n,c+n)])
    tetra=sorted(set(tuple(sorted(t)) for t in tetra))
    simplices=[[(i,) for i in range(len(xyz))],
        sorted({e for t in tetra for e in combinations(t,2)}),
        sorted({f for t in tetra for f in combinations(t,3)}),tetra]
    maps=[{t:i for i,t in enumerate(s)} for s in simplices]
    D=[]
    for k in range(3):
        a=np.zeros((len(simplices[k+1]),len(simplices[k])),dtype=np.int64)
        for i,t in enumerate(simplices[k+1]):
            for j in range(len(t)):a[i,maps[k][t[:j]+t[j+1:]]]=(-1)**j
        D.append(a)
    assert not np.any(D[1]@D[0]) and not np.any(D[2]@D[1])
    return xyz,simplices,maps,D

def whitney(xyz,simplices,maps,epsilon=epsilon_0,mu=mu_0):
    """Consistent full Hodge masses for edge E and face magnetic flux.
    Four-point degree-two tetrahedral rule is exact for affine Whitney forms.
    """
    assert epsilon>0 and mu>0
    E=np.zeros((len(simplices[1]),)*2); B=np.zeros((len(simplices[2]),)*2)
    a=(5+3*np.sqrt(5))/20;b=(5-np.sqrt(5))/20
    quadrature=np.full((4,4),b); np.fill_diagonal(quadrature,a)
    volume=0.
    for tet in simplices[3]:
        p=xyz[list(tet)]; V=abs(np.linalg.det((p[1:]-p[0]).T))/6
        assert V>0; volume+=V
        # Center and scale before inversion to avoid Earth-radius cancellation.
        scale=np.max(np.linalg.norm(p-p[0],axis=1))
        G=np.linalg.inv(np.column_stack((np.ones(4),(p-p[0])/scale)))[1:,:].T/scale
        edges=list(combinations(range(4),2)); faces=list(combinations(range(4),3))
        ei=[maps[1][tuple(tet[i] for i in e)] for e in edges]
        fi=[maps[2][tuple(tet[i] for i in f)] for f in faces]
        for l in quadrature:
            w=np.array([l[i]*G[j]-l[j]*G[i] for i,j in edges])
            q=np.array([2*(l[i]*np.cross(G[j],G[k])+l[j]*np.cross(G[k],G[i])+l[k]*np.cross(G[i],G[j])) for i,j,k in faces])
            E[np.ix_(ei,ei)]+=epsilon*V/4*(w@w.T)
            B[np.ix_(fi,fi)]+=V/(4*mu)*(q@q.T)
    return E,B,volume

def normalized(D,E,B):
    """xE=LE.T Efield, xB=LB.T flux; no diagonal Hodge approximation."""
    LE=cholesky(E,lower=True); LB=cholesky(B,lower=True)
    C=solve_triangular(LE,(LB.T@D[1]).T,lower=True).T
    K=np.block([[np.zeros_like(E),C.T],[-C,np.zeros_like(B)]])
    return K,LE,LB

def physical_fields(x,LE,LB):
    ne=len(LE); return solve_triangular(LE.T,x[:ne]),solve_triangular(LB.T,x[ne:])

def verify(radii,levels=0):
    xyz,s,m,D=shell_mesh(radii,levels); E,B,V=whitney(xyz,s,m)
    K,LE,LB=normalized(D,E,B); rng=np.random.default_rng(369)
    x=rng.normal(size=len(K)); e,b=physical_fields(x,LE,LB)
    assert np.allclose(x@x,e@E@e+b@B@b)
    assert np.array_equal(K,-K.T)
    # Magnetic Gauss invariant and electric gauge-gradient nullspace.
    assert np.allclose(D[2]@D[1],0)
    grad=LE.T@D[0]
    assert np.linalg.norm(K[len(E):,:len(E)]@grad)<=1e-10*max(1.,np.linalg.norm(K)*np.linalg.norm(grad))
    return dict(vertices=len(xyz),edges=len(E),faces=len(B),tetrahedra=len(s[3]),
                volume_m3=V,energy_residual=float(x@K@x),physical_admission=False,
                warning='consistent Hodge inverse is nonlocal; not a local cone propagator')

if __name__=='__main__':
    import json
    print(json.dumps([verify([6371000.,6426000.,6481000.],k) for k in (0,1)],indent=2))
