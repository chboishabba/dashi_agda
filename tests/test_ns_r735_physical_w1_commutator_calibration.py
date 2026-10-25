"""Numerical SAME-HELICAL-FIELD W1 commutator calibration, not a proof.

R691/R735 original source: nonlinear projected Galerkin N(u) and
M=H+u x H-u. For D_nl M=H+N x H-u + H+u x H-N,
C_N=2 Re sum_k <M_k,D_nl M_k>.
Cauchy gives |C_N|²<=4||M||_2²||D_nl M||_2².
H± L4 multipliers + sharp-cube boundedness + H^(3/4)->L4
imply a cutoff-independent smooth-trajectory conditional upper bound
|C_N| <= C||u_N||_(H^(3/4))³||N_N||_(H^(3/4)).
This does NOT independently bound these norms in time, prove R735
W1/W2 on arbitrary solutions, or establish Clay B.

This test is deliberately float64 with explicit tolerances: full
symbolic simplification on all helical triads timed out locally.
"""
from collections import defaultdict
import numpy as np

p=(1,0,0);q=(0,1,2);k=(1,1,2)
def neg(m):return tuple(-a for a in m)
def norm2(m):return sum(a*a for a in m)
def helical(m,v,sign):
    a=np.array(m,dtype=float)
    return (v+sign*1j*np.cross(a,v)/np.linalg.norm(a))/2
def seed():
    u={p:np.array([0,1,1],dtype=complex),
       q:np.array([1,0,0],dtype=complex),
       k:1j*np.array([1,-1,0],dtype=complex)}
    u.update({neg(m):np.conj(v) for m,v in list(u.items())})
    return u
def physical_projected_nonlinear(u):
    c=defaultdict(lambda:np.zeros(3,dtype=complex))
    for p,up in u.items():
        for q,uq in u.items():
            m=tuple(p[i]+q[i] for i in range(3))
            c[m]+=np.dot(q,up)*uq
    out={}
    for m,v in c.items():
        if norm2(m)==0:continue
        a=np.array(m,dtype=float)
        out[m]=-1j*(v-a*np.dot(a,v)/norm2(m))
    return out
def mixed(u):
    out=defaultdict(lambda:np.zeros(3,dtype=complex))
    for p,up in u.items():
        for q,uq in u.items():
            m=tuple(p[i]+q[i] for i in range(3))
            out[m]+=np.cross(helical(p,up,1),helical(q,uq,-1))
    return out
def nonlinear_mixed_derivative(u,N):
    out=defaultdict(lambda:np.zeros(3,dtype=complex))
    for p,up in u.items():
        for q,nq in N.items():
            m=tuple(p[i]+q[i] for i in range(3))
            out[m]+=np.cross(helical(p,up,1),helical(q,nq,-1))
    for p,np_ in N.items():
        for q,uq in u.items():
            m=tuple(p[i]+q[i] for i in range(3))
            out[m]+=np.cross(helical(p,np_,1),helical(q,uq,-1))
    return out
def receipt(u):
    M=mixed(u);d=nonlinear_mixed_derivative(u,physical_projected_nonlinear(u))
    E=sum(np.vdot(v,v).real for v in M.values())
    D=sum(np.vdot(v,v).real for v in d.values())
    C=2*sum(np.vdot(v,d[m]).real for m,v in M.items())
    return C,E,D

def test_physical_commutator_cauchy_and_quintic_scaling():
    u=seed();C,E,D=receipt(u)
    assert E>0 and D>0 and abs(C)>1e-8
    assert C*C<=4*E*D*(1+1e-12)
    for a in (-2,-1,2):
        c,e,d=receipt({m:a*v for m,v in u.items()})
        assert np.isclose(c,a**5*C,rtol=1e-11,atol=1e-9)
        assert np.isclose(e,a**4*E,rtol=1e-11,atol=1e-9)
        assert np.isclose(d,a**6*D,rtol=1e-11,atol=1e-9)

def test_projected_nonlin_transverse_and_reality_paired():
    n=physical_projected_nonlinear(seed())
    for m,v in n.items():
        assert np.isclose(np.dot(m,v),0,atol=1e-12)
        assert np.allclose(n[neg(m)],np.conj(v),atol=1e-12)
