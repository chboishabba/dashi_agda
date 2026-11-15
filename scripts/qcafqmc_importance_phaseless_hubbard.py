#!/usr/bin/env python3
"""Finite discrete-HS importance/force-bias/phaseless projector control.
Hirsch PRB 28 (1983), IonQ QC-AFQMC: arXiv:2611.08129.
Not an original nickel, 16-qubit shadow or scalable production AFQMC run.
"""
import argparse
import json
import numpy as np

def setup(U=4.0,dt=.025):
    k=np.array([[0.,-1.],[-1.,0.]])
    e,v=np.linalg.eigh(k)
    half=(v*np.exp(-dt*e/2))@v.T
    gamma=np.arccosh(np.exp(dt*U/2))
    ops=[]
    for s0 in (-1,1):
        for s1 in (-1,1):
            s=np.array([s0,s1])
            a=half@np.diag(np.exp(gamma*s))@half
            b=half@np.diag(np.exp(-gamma*s))@half
            ops.append(np.kron(a,b)*np.exp(-dt*U))
    ops=np.array(ops)
    H=np.kron(k,np.eye(2))+np.kron(np.eye(2),k)+np.diag([U,0.,0.,U])
    return H,ops.mean(axis=0),ops,np.ones(4)/2,float(np.linalg.eigvalsh(H)[0])

def systematic_resample(weights,rng):
    cdf=np.cumsum(weights/weights.sum());cdf[-1]=1.
    positions=(rng.random()+np.arange(len(weights)))/len(weights)
    return np.searchsorted(cdf,positions)

def run(seed=19,walkers=1000,steps=32,force_bias=True,phaseless=True,
        branch_every=4,complex_trial=False):
    rng=np.random.default_rng(seed)
    H,T,ops,psi0,ground=setup()
    trial=psi0.astype(complex)
    if complex_trial:
        trial*=np.exp(1j*np.array([.1,-.3,.25,-.1]))
    trial/=np.linalg.norm(trial)
    states=np.tile(psi0,(walkers,1)).astype(complex)
    states/=((states@trial.conj())[:,None])
    weights=np.ones(walkers)
    exact=psi0.copy()
    history=[]
    for step in range(1,steps+1):
        candidate=np.einsum('fij,nj->nfi',ops,states)
        z=np.einsum('nfi,i->nf',candidate,trial.conj())
        if force_bias:
            q=np.maximum(np.abs(z),1e-300)
            q/=q.sum(axis=1,keepdims=True)
        else:
            q=np.full((walkers,4),.25)
        selected=np.minimum(3,np.sum(rng.random(walkers)[:,None]>np.cumsum(q,axis=1),axis=1))
        row=np.arange(walkers)
        overlap=z[row,selected]
        factor=overlap*(.25/q[row,selected])
        if phaseless:
            weights*=np.abs(factor)*np.maximum(0,np.cos(np.angle(factor)))
        else:
            # Deliberately invalid magnitude-only negative control, NOT free projection.
            weights*=np.abs(factor)
        states=candidate[row,selected]/overlap[:,None]
        exact=T@exact
        if branch_every and step%branch_every==0:
            if weights.sum()<=0:raise RuntimeError("all walkers died")
            states=states[systematic_resample(weights,rng)]
            weights=np.ones(walkers)
        local=states@(H.T@trial.conj())
        energy=float(np.real(np.dot(weights,local)/weights.sum()))
        reference=float(np.real((trial.conj()@H@exact)/(trial.conj()@exact)))
        history.append({"step":step,"sampled_mixed_energy":energy,
                        "exact_trotter_mixed_energy":reference,
                        "absolute_error":abs(energy-reference),
                        "effective_sample_size":float(weights.sum()**2/np.dot(weights,weights))})
    return {"scope":"finite two-site Hubbard discrete HS; not IonQ chemistry",
            "seed":seed,"walkers":walkers,"steps":steps,"force_bias":force_bias,
            "phaseless":phaseless,"complex_trial":complex_trial,
            "ground_energy":ground,"final":history[-1],"history":history}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--walkers",type=int,default=1000)
    p.add_argument("--steps",type=int,default=32)
    p.add_argument("--seed",type=int,default=19)
    p.add_argument("--complex-trial",action="store_true")
    a=p.parse_args()
    print(json.dumps(run(seed=a.seed,walkers=a.walkers,steps=a.steps,
                         complex_trial=a.complex_trial),indent=2))
