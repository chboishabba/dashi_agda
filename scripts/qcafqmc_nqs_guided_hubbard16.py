#!/usr/bin/env python3
"""Finite 16-qubit NQS-guided auxiliary-field projector.

Hubbard *subclass* of FCIDUMP: general 8x8 one-body h and on-site U_i only.
Walker Slater overlaps and local energies use the same physical FCI Hamiltonian
as the trained fixed-sector NQS. Not the original nickel/upCCD calculation.

Attribution: Hirsch, Phys Rev B 28 (1983); Provazza et al.
arXiv:2611.08129; prior DASHI finite-Hubbard controls.
"""
import argparse
import json
from itertools import product
import numpy as np
from qcafqmc_molecular_fcidump import parse_fcidump, fci_matrix, slater_amplitudes
from qcafqmc_nqs_fci_same_source import trial_from_checkpoint, walker_mixed_energy

def density_hs_operators(h,eri,dt,tolerance=1e-10):
    n=len(h)
    U=np.array([eri[i,i,i,i] for i in range(n)])
    if np.any(U < -tolerance):
        raise ValueError("negative on-site U unsupported in this control")
    projected=np.zeros_like(eri)
    for i in range(n):projected[i,i,i,i]=U[i]
    if np.linalg.norm(eri-projected)>tolerance:
        raise ValueError("nonlocal/offsite two-electron integrals require molecular Cholesky AFQMC via ipie")
    active=np.flatnonzero(U>tolerance)
    if len(active)>8:
        raise ValueError("unsafe 2**N Hubbard fields")
    e,v=np.linalg.eigh(h)
    half=(v*np.exp(-dt*e/2))@v.T
    gamma=np.arccosh(np.exp(dt*np.maximum(U,0)/2))
    fields=list(product((-1.,1.),repeat=len(active)))
    operators=[]
    for values in fields:
        spins=np.zeros(n)
        spins[active]=values
        a=half@np.diag(np.exp(-dt*U/2+gamma*spins))@half
        b=half@np.diag(np.exp(-dt*U/2-gamma*spins))@half
        operators.append((a,b))
    return operators,active

def amplitudes(alpha,beta,states):
    return slater_amplitudes(alpha,beta,states)

def choose(weights,rng):
    cumulative=np.cumsum(weights/weights.sum());cumulative[-1]=1.
    return int(np.searchsorted(cumulative,rng.random(),side="right"))

def run(integrals,checkpoint,walkers=80,steps=16,dt=.015,seed=23,
        branch_every=4,phaseless=True):
    h,eri,na,nb,core=parse_fcidump(integrals)
    if len(h)!=8:raise ValueError("expected 16 spin-orbitals/8 spatial orbitals")
    H,states=fci_matrix(h,eri,na,nb,core)
    if len(states)>5000:raise ValueError("sector too large")
    trial,_=trial_from_checkpoint(checkpoint,states,len(h),na,nb)
    ops,active=density_hs_operators(h,eri,dt)
    e,v=np.linalg.eigh(h)
    initial_a=v[:,:na].astype(complex)
    initial_b=v[:,:nb].astype(complex)
    base=amplitudes(initial_a,initial_b,states)
    base_overlap=np.vdot(trial,base)
    if abs(base_overlap)<1e-8:
        raise ValueError("initial trial overlap is too small")
    # Divide one spin orbital by overlap to fix gauge/normalization.
    # For the empty-alpha sector normalize a beta orbital instead.
    if na:
        initial_a[:,0]/=base_overlap
    elif nb:
        initial_b[:,0]/=base_overlap
    else:raise ValueError("empty-electron vacuum is not the target")
    population=[(initial_a.copy(),initial_b.copy()) for _ in range(walkers)]
    rng=np.random.default_rng(seed)
    history=[]
    weights=np.ones(walkers)
    for step in range(1,steps+1):
        proposed=[]
        new_weights=np.zeros(walkers)
        for index,(alpha,beta) in enumerate(population):
            choices=[]
            for aa,bb in ops:
                a=aa@alpha;b=bb@beta
                amplitude=amplitudes(a,b,states)
                ratio=np.vdot(trial,amplitude)
                choices.append((a,b,ratio))
            importance=np.array([abs(item[2]) for item in choices])
            if importance.sum()<1e-14:
                raise RuntimeError("zero overlap on all HS branches")
            q=importance/importance.sum()
            pick=choose(q,rng)
            a,b,ratio=choices[pick]
            factor=ratio/(len(ops)*q[pick])
            if phaseless:
                factor_weight=abs(factor)*max(0.,np.cos(np.angle(factor)))
            else:
                raise ValueError("complex free-projection requires phase-weight tracking")
            new_weights[index]=weights[index]*factor_weight
            if abs(ratio)<1e-12:
                raise RuntimeError("selected near-node walker")
            if na:a[:,0]/=ratio
            else:b[:,0]/=ratio
            proposed.append((a,b))
        weights=new_weights
        population=proposed
        if weights.sum()<=0:raise RuntimeError("population collapsed")
        local=np.array([
            walker_mixed_energy(H,trial,amplitudes(a,b,states))
            for a,b in population])
        energy=np.dot(weights,local)/weights.sum()
        effective=weights.sum()**2/np.dot(weights,weights)
        history.append({"step":step,"mixed_energy_real":float(energy.real),
                        "mixed_energy_imag":float(energy.imag),
                        "effective_sample_size":float(effective)})
        if branch_every and step%branch_every==0:
            cumulative=np.cumsum(weights/weights.sum())
            positions=(rng.random()+np.arange(walkers))/walkers
            selected=np.searchsorted(cumulative,positions)
            population=[(population[i][0].copy(),population[i][1].copy())
                        for i in selected]
            weights=np.ones(walkers)
    return {"scope":"finite 16-qubit NQS-guided *onsite Hubbard* AFQMC",
            "source_integrals":str(integrals),"source_checkpoint":str(checkpoint),
            "original_ionq_nickel_replication":False,
            "walkers":walkers,"steps":steps,"dt":dt,"seed":seed,
            "field_count":len(ops),"active_interacting_sites":active.tolist(),
            "FCI_ground_energy":float(np.linalg.eigvalsh(H)[0]),
            "history":history}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("fcidump");p.add_argument("nqs_checkpoint")
    p.add_argument("--walkers",type=int,default=80)
    p.add_argument("--steps",type=int,default=16)
    p.add_argument("--dt",type=float,default=.015)
    p.add_argument("--seed",type=int,default=23)
    a=p.parse_args()
    print(json.dumps(run(a.fcidump,a.nqs_checkpoint,a.walkers,a.steps,
                         a.dt,a.seed),indent=2))
