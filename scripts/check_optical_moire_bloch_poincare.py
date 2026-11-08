#!/usr/bin/env python3
"""DASHI original finite Bloch and Poincare bridge, not original optical research.
Dev & Shen (2026): DOI 10.1038/s41377-026-02533-w.
Graphene/condensed matter owns its separate Bloch bands and reciprocal lattice.
"""
import json
import numpy as np

def stokes(j):
    x,y=np.asarray(j,complex)
    power=(abs(x)**2+abs(y)**2)
    if power<1e-12: raise ValueError("Stokes undefined at Jones null")
    return np.array([2*(x.conjugate()*y).real,2*(x.conjugate()*y).imag,abs(x)**2-abs(y)**2])/power

def fidelity(u,v):
    u=np.asarray(u,complex);v=np.asarray(v,complex)
    return abs(np.vdot(u,v))**2/(np.vdot(u,u).real*np.vdot(v,v).real)

def translation_residual(points,coeff,R,k0=(0.,0.)):
    q=np.asarray(points,float);c=np.asarray(coeff,complex)
    mask=np.sum(abs(c)**2,axis=-1)>1e-22
    phase=np.exp(1j*q[mask]@R)
    target=np.exp(1j*np.dot(k0,R))
    return float(np.linalg.norm(c[mask]*(phase[:,None]-target))/np.linalg.norm(c[mask]))

def test():
    rng=np.random.default_rng(13)
    norm_error=phase_error=overlap_error=0.
    for _ in range(100):
        u=rng.normal(size=2)+1j*rng.normal(size=2)
        v=rng.normal(size=2)+1j*rng.normal(size=2)
        alpha=rng.uniform(-np.pi,np.pi)
        su,sv=stokes(u),stokes(v)
        norm_error=max(norm_error,abs(np.linalg.norm(su)-1))
        phase_error=max(phase_error,float(np.max(abs(su-stokes(np.exp(1j*alpha)*u)))))
        overlap_error=max(overlap_error,abs(fidelity(u,v)-.5*(1+np.dot(su,sv))))
    G=np.array([[0,0],[2*np.pi,0],[-2*np.pi,0],[0,2*np.pi],[2*np.pi,2*np.pi]])
    k0=np.array([.31,-.17]);q=G+k0
    c=rng.normal(size=(5,2))+1j*rng.normal(size=(5,2))
    comm=max(translation_residual(q,c,np.array(t),k0) for t in ((1,0),(0,1),(1,1),(2,-3)))
    q2=np.concatenate((q,[[k0[0]+2*np.pi*np.sqrt(2),k0[1]]]))
    c2=np.concatenate((c,np.array([[1+0j,.25+0j]])))
    not_bloch=translation_residual(q2,c2,np.array([1.,0.]),k0)
    assert max(norm_error,phase_error,overlap_error,comm)<1e-12
    assert not_bloch>.05
    return {"original_attribution":"Dev and Shen (2026) DOI 10.1038/s41377-026-02533-w",
        "DASHI_role":"independent finite Jones/Poincare and Bloch translation test",
        "polarization_fixtures":100,"norm_error":norm_error,"phase_error":phase_error,
        "fidelity_error":overlap_error,"commensurate_residual":comm,
        "selected_incommensurate_translation_residual":not_bloch,
        "global_aperiodicity_not_proven":True,"experiment_reproduced":False}

if __name__=="__main__":print(json.dumps(test(),indent=2))
