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


# Canonical output-cutoff acceptance: R691/R735 sums the source-selected
# output list, NOT all p+q generated outputs from the input cube.
# The latter is useful diagnostic algebra but NOT the signed W1 consumer.
def selected_output_work(u,cutoff):
    assert all(max(map(abs,k))<=cutoff for k in u)
    forcing=projected_nonlinear(u,cutoff=cutoff)
    M=mixed(u,u); one=mixed(forcing,u); two=mixed(u,forcing)
    Q={k:one.get(k,np.zeros(3,complex))+two.get(k,np.zeros(3,complex))
       for k in set(one)|set(two)}
    selected={k for k in M if norm2(k)>0 and max(map(abs,k))<=cutoff}
    all_outputs={k for k in M if norm2(k)>0}
    def work(keys):
        return 2*sum(np.vdot(M[k],Q.get(k,np.zeros(3,complex))).real
                     for k in keys)
    EM=sum(np.vdot(M[k],M[k]).real for k in selected)
    EQ=sum(np.vdot(Q.get(k,np.zeros(3,complex)),
                   Q.get(k,np.zeros(3,complex))).real for k in selected)
    return work(selected),work(all_outputs),EM,EQ,selected,M,Q,forcing


def test_selected_output_sign_is_not_full_convolution_sign():
    selected,full,EM,EQ,modes,*_=selected_output_work(seed(),2)
    assert len(modes)==12
    assert selected<0<full
    assert np.isclose(selected,-9.849528420767435,atol=1e-10)
    assert np.isclose(full,1.200843362231229,atol=1e-10)
    assert abs(selected-full)>10
    # This is the exact selected-source Hilbert Cauchy inequality,
    # independent of the sign of its physical commutator.
    assert selected**2 <= 4*EM*EQ*(1+1e-12)


def test_selected_output_Leibniz_derivative_same_Galerkin_velocity():
    u=seed();cutoff=2
    c,full,EM,EQ,selected,M,Q,F=selected_output_work(u,cutoff)
    eps=1e-5
    def nudged(sign):
        return {k:u.get(k,np.zeros(3,complex))
                 +sign*eps*F.get(k,np.zeros(3,complex))
                for k in set(u)|set(F)}
    def selected_mass(field):
        terms=mixed(field,field)
        return sum(np.vdot(terms.get(k,np.zeros(3,complex)),
                           terms.get(k,np.zeros(3,complex))).real
                   for k in selected)
    numeric_derivative=(selected_mass(nudged(+1))-selected_mass(nudged(-1)))/(2*eps)
    assert np.isclose(c,numeric_derivative,rtol=3e-7,atol=2e-7)
    assert not np.isclose(full,numeric_derivative,atol=0.1)


def test_full_output_and_selected_output_agree_when_selection_includes_support():
    # At cutoff 4 the same physical datum has no discarded mixed mode;
    # the forcing must independently be recalculated at cutoff 4.
    selected,full,EM,EQ,modes,*_=selected_output_work(seed(),4)
    assert len(modes)==18
    assert np.isclose(selected,full,atol=1e-10)
    assert np.isclose(selected,2.5523607586812247,atol=1e-10)
