#!/usr/bin/env python3
"""Two-site Hubbard multi-step auxiliary-field projector with exact controls.

Source attribution: J. E. Hirsch, Phys Rev B 28, 4059 (1983).
Motivation: Provazza, Knitter et al., arXiv:2611.08129 (2026).
This is NOT nickel chemistry or phaseless AFQMC.
"""
import json
import numpy as np

def run(seed=261108129, samples=50000, steps=12, dt=0.025, U=4.):
    rng = np.random.default_rng(seed)
    k = np.array([[0.,-1.],[-1.,0.]])
    ev, vec = np.linalg.eigh(k)
    half = (vec*np.exp(-dt*ev/2))@vec.T
    gamma = np.arccosh(np.exp(dt*U/2))
    K = np.kron(k,np.eye(2))+np.kron(np.eye(2),k)
    H = K + np.diag([U,0.,0.,U])
    alpha_ops=[]; beta_ops=[]
    for s0 in (-1,1):
        for s1 in (-1,1):
            s=np.array([s0,s1])
            alpha_ops.append(half@np.diag(np.exp(gamma*s))@half)
            beta_ops.append(half@np.diag(np.exp(-gamma*s))@half)
    A=np.array(alpha_ops); B=np.array(beta_ops)
    T=np.exp(-dt*U)*sum(np.kron(a,b) for a,b in zip(A,B))/4
    ke,kv=np.linalg.eigh(K)
    Khalf=(kv*np.exp(-dt*ke/2))@kv.T
    Tref=Khalf@np.diag(np.exp(-dt*np.diag(H-K)))@Khalf
    hs_error=float(np.linalg.norm(T-Tref))
    assert hs_error<1e-12
    orbital=np.ones(2)/np.sqrt(2)
    psi0=np.kron(orbital,orbital)
    trial=psi0.copy()
    alpha=np.tile(orbital,(samples,1))
    beta=np.tile(orbital,(samples,1))
    exact=psi0.copy()
    history=[]
    for n in range(1,steps+1):
        field=rng.integers(4,size=samples)
        alpha=np.einsum('nij,nj->ni',A[field],alpha)
        beta=np.einsum('nij,nj->ni',B[field],beta)
        sampled=np.exp(-n*dt*U)*(alpha[:,:,None]*beta[:,None,:]).reshape(samples,4).mean(axis=0)
        exact=T@exact
        energy=float((trial@H@sampled)/(trial@sampled))
        exact_energy=float((trial@H@exact)/(trial@exact))
        history.append({"step":n,"sampled_energy":energy,"trotter_energy":exact_energy,
                        "energy_error":abs(energy-exact_energy),
                        "state_l2_error":float(np.linalg.norm(sampled-exact))})
    wrong_normalization=float(np.linalg.norm(sum(np.kron(a,b) for a,b in zip(A,B))/4-Tref))
    wrong_gamma=float(np.linalg.norm(np.exp(-dt*U)*np.kron(half@half,half@half)-Tref))
    assert wrong_normalization>1e-3 and wrong_gamma>1e-3
    assert history[-1]["state_l2_error"]<0.015
    assert history[-1]["energy_error"]<0.08
    evals, evecs=np.linalg.eigh(H)
    continuous=(evecs*np.exp(-steps*dt*evals))@evecs.T@psi0
    return {"scope":"finite Hubbard HS projector, not IonQ replication",
            "seed":seed,"samples":samples,"steps":steps,"dt":dt,"U":U,
            "ground_energy":float(evals[0]),"hs_fro_error":hs_error,
            "wrong_normalization_fro_error":wrong_normalization,
            "wrong_gamma_fro_error":wrong_gamma,
            "exact_continuous_mixed_energy":float((trial@H@continuous)/(trial@continuous)),
            "history":history}

if __name__ == "__main__":
    print(json.dumps(run(),indent=2))
