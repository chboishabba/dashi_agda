#!/usr/bin/env python3
"""Source-specific seniority-zero diagonalization (DOCI), 8e/8o nickel baseline.

DOCI is the exact variational ground state *within* the zero-seniority
subspace, NOT upCCD and NOT exact unrestricted FCI. It is a valuable
independent classical trial against which HF and shadow-learned NQS may be
compared with the same FCIDUMP integral source.

Physical attribution: seniority-zero CI / doubly occupied configuration
interaction (DOCI); Slater-Condon second quantization; existing DASHI
qcafqmc_molecular_fcidump.py operator definitions.
"""
import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path
import numpy as np
from qcafqmc_molecular_fcidump import parse_fcidump, apply_ops

def paired_sector(n,n_pairs):
    if n_pairs<0 or n_pairs>n:raise ValueError("invalid pair count")
    occupied=list(combinations(range(n),n_pairs))
    states=[]
    for sites in occupied:
        mask=sum(1<<i for i in sites)
        states.append(mask|(mask<<n))
    return states,occupied

def doci_hamiltonian(h,eri,n_pairs,ecore=0.,threshold=1.e-12):
    h=np.asarray(h);eri=np.asarray(eri);n=h.shape[0]
    if (h.shape!=(n,n) or eri.shape!=(n,n,n,n)
            or not np.isfinite(h).all() or not np.isfinite(eri).all()):
        raise ValueError("invalid electronic tensors")
    if not np.allclose(h,h.conj().T,atol=1e-9):
        raise ValueError("one-body Hamiltonian not Hermitian")
    if not np.allclose(eri,eri.transpose(2,3,0,1).conj(),atol=1e-9):
        raise ValueError("electron repulsion tensor lacks pair interchange")
    states,occupations=paired_sector(n,n_pairs)
    lookup={state:i for i,state in enumerate(states)}
    matrix=np.eye(len(states),dtype=np.result_type(h,eri,complex))*ecore

    one=[(p+spin*n,q+spin*n,h[p,q])
         for spin in (0,1) for p in range(n) for q in range(n)
         if abs(h[p,q])>threshold]
    two=[(p+spin*n,q+spin*n,r+other*n,s+other*n,.5*eri[p,q,r,s])
         for spin in (0,1) for other in (0,1)
         for p in range(n) for q in range(n)
         for r in range(n) for s in range(n)
         if abs(eri[p,q,r,s])>threshold]
    for column,state in enumerate(states):
        for p,q,weight in one:
            target,phase=apply_ops(state,((q,False),(p,True)))
            if target in lookup:matrix[lookup[target],column]+=weight*phase
        for p,q,r,s,weight in two:
            target,phase=apply_ops(state,((q,False),(s,False),(r,True),(p,True)))
            if target in lookup:matrix[lookup[target],column]+=weight*phase
    if not np.allclose(matrix,matrix.conj().T,atol=1e-9):
        raise ValueError("projected electronic Hamiltonian is not Hermitian")
    return matrix,occupations

def source_doci(fcidump,receipt_file=None,save=None):
    h,eri,na,nb,ecore=parse_fcidump(fcidump)
    if na!=nb:raise ValueError("DOCI requires equal alpha/beta pair count")
    if len(h)!=8 or na!=4:
        raise ValueError("nickel DOCI target is eight spatial orbitals/four pairs")
    receipt=None
    if receipt_file is not None:
        receipt=json.loads(Path(receipt_file).read_text())
        if receipt.get("integral_sha256")!=hashlib.sha256(Path(fcidump).read_bytes()).hexdigest():
            raise ValueError("FCIDUMP mismatches source receipt")
        if not receipt.get("selected_mo_sha256") or not receipt.get("geometry_sha256"):
            raise ValueError("source MO/geometry fingerprints absent")
    H,occupation=doci_hamiltonian(h,eri,4,ecore)
    eigenvalues,vectors=np.linalg.eigh(H)
    result={"scope":"DOCI 70-state seniority-zero projected electronic Hamiltonian",
            "fcidump":str(fcidump),
            "fcidump_sha256":hashlib.sha256(Path(fcidump).read_bytes()).hexdigest(),
            "geometry_sha256":receipt.get("geometry_sha256") if receipt else None,
            "orbital_frame_sha256":receipt.get("selected_mo_sha256") if receipt else None,
            "paired_dimension":len(occupation),
            "DOCI_energy_hartree":float(eigenvalues[0]),
            "trial_upccd":False,"trial_original_ionq":False,
            "DOCI_variational_subspace":True}
    if save is not None:
        save=Path(save).resolve()
        save.parent.mkdir(parents=True,exist_ok=True)
        coefficient=vectors[:,0]
        np.savez(save,coefficients=coefficient,
                 occ_alpha=np.array(occupation,dtype=np.int32),
                 occ_beta=np.array(occupation,dtype=np.int32),
                 fcidump_sha256=result["fcidump_sha256"],
                 geometry_sha256=result["geometry_sha256"] or "",
                 orbital_frame_sha256=result["orbital_frame_sha256"] or "",
                 source_kind="independent-DOCI")
        result["trial_npz"]=str(save)
    return result

def self_test():
    # Independent paired matrix check against the existing general FCI
    # definition for 2-site 1+1 Hubbard.
    from qcafqmc_molecular_fcidump import fci_matrix,hubbard_fixture
    h,eri,na,nb,c=hubbard_fixture()
    projected,paired=doci_hamiltonian(h,eri,1,c)
    full,states=fci_matrix(h,eri,1,1,c)
    bits=[sum(1<<i for i in occ)*(1+(1<<len(h))) for occ in paired]
    index=[states.index(x) for x in bits]
    assert np.allclose(projected,full[np.ix_(index,index)],atol=1e-12)
    assert np.allclose(np.linalg.eigvalsh(projected),[4.,4.])
    assert np.linalg.eigvalsh(full)[0] < np.linalg.eigvalsh(projected)[0]
    return {"small_hubbard_projected_matrix_matches_FCI":True,
            "DOCI_ground_energy":float(np.linalg.eigvalsh(projected)[0]),
            "full_FCI_ground_energy":float(np.linalg.eigvalsh(full)[0]),
            "seniority_zero_approximation_gap_positive":True}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--fcidump")
    p.add_argument("--receipt")
    p.add_argument("--save")
    a=p.parse_args()
    print(json.dumps(source_doci(a.fcidump,a.receipt,a.save)
                     if a.fcidump else self_test(),indent=2))
