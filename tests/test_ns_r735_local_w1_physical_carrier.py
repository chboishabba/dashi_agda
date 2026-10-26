"""Physical finite Galerkin same-object W1 contact (numerical, not kernel proof).

Tests the actual Leray-projected NS quadratic forcing, original normalised
H+/H- helical projectors, mixed incidence convolution and the *derivative*
Q=dM/dt|nonlinear on a real, divergence-free finite Fourier field.
The local H1/H2 bound is mathematical harmonic analysis, NOT numerically
proved by the assertions below.
"""
from collections import defaultdict
import numpy as np


def neg(k): return tuple(-x for x in k)
def norm2(k): return sum(x*x for x in k)
def h(k,v,sign):
    kvec=np.asarray(k,dtype=float)
    assert norm2(k)>0
    return 0.5*(v+sign*1j*np.cross(kvec,v)/np.linalg.norm(kvec))
def seed():
    u={(1,0,0):np.array([0,1,1],complex),
       (0,1,2):np.array([1,0,0],complex),
       (1,1,2):np.array([1j,-1j,0],complex)}
    u.update({neg(k):np.conj(v) for k,v in list(u.items())})
    return u

def projected_nonlinear(u,cutoff=None):
    raw=defaultdict(lambda:np.zeros(3,complex))
    for p,up in u.items():
        for q,uq in u.items():
            k=tuple(p[i]+q[i] for i in range(3))
            raw[k]+=np.dot(q,up)*uq
    N={}
    for k,a in raw.items():
        if norm2(k)==0 or (cutoff is not None and max(map(abs,k))>cutoff):continue
        kv=np.asarray(k,dtype=float)
        N[k]=-1j*(a-kv*np.dot(kv,a)/norm2(k))
    return N

def mixed(a,b):
    out=defaultdict(lambda:np.zeros(3,complex))
    for p,up in a.items():
        for q,uq in b.items():
            if norm2(p)==0 or norm2(q)==0:continue
            k=tuple(p[j]+q[j] for j in range(3))
            out[k]+=np.cross(h(p,up,+1),h(q,uq,-1))
    return out

def mass(a): return sum(np.vdot(v,v).real for v in a.values())

def test_same_physical_N_and_Q_are_reality_transverse():
    u=seed();N=projected_nonlinear(u,cutoff=4)
    assert N
    for k,v in N.items():
        assert abs(np.dot(k,v))<1e-12
        assert np.allclose(N[neg(k)],np.conj(v),atol=1e-12)
    for k,v in u.items():
        assert np.allclose(h(k,v,+1)+h(k,v,-1),v,atol=1e-12)

def test_nonlin_helical_mixed_derivative_exact_bilinear_polynomial():
    u=seed();N=projected_nonlinear(u,cutoff=4)
    M=mixed(u,u)
    term1=mixed(N,u);term2=mixed(u,N)
    Q={k:term1.get(k,np.zeros(3,complex))+term2.get(k,np.zeros(3,complex))
       for k in set(term1)|set(term2)}
    quad=mixed(N,N)
    for eps in (0.125,-0.25,0.5):
        perturbed={k:u.get(k,np.zeros(3,complex))+eps*N.get(k,np.zeros(3,complex))
                   for k in set(u)|set(N)}
        mp=mixed(perturbed,perturbed)
        for k in set(M)|set(Q)|set(quad)|set(mp):
            expected=(M.get(k,np.zeros(3,complex))+
                      eps*Q.get(k,np.zeros(3,complex))+
                      eps*eps*quad.get(k,np.zeros(3,complex)))
            assert np.allclose(mp.get(k,np.zeros(3,complex)),expected,atol=5e-12)

    cm=2*sum(np.vdot(v,Q.get(k,np.zeros(3,complex))).real for k,v in M.items())
    assert abs(cm)>1e-8
    eps=1e-5
    plus={k:u.get(k,np.zeros(3,complex))+eps*N.get(k,np.zeros(3,complex)) for k in set(u)|set(N)}
    minus={k:u.get(k,np.zeros(3,complex))-eps*N.get(k,np.zeros(3,complex)) for k in set(u)|set(N)}
    derivative=(mass(mixed(plus,plus))-mass(mixed(minus,minus)))/(2*eps)
    assert np.isclose(cm,derivative,rtol=3e-7,atol=1e-7)
