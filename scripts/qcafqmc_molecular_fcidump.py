#!/usr/bin/env python3
"""Physical finite-orbital second-quantized electronic Hamiltonian.

FCIDUMP spatial chemists' integrals (pq|rs), real restricted orbitals.
Attribution: standard electronic structure second quantization; Molpro FCIDUMP
convention. Reuses DASHI atomic/369 fermionic occupation distinction.
Never treats ternary labels as chemical integral measurements.
"""
import argparse
import itertools
import json
import re
from pathlib import Path
import numpy as np

def parse_fcidump(path):
    text=Path(path).read_text()
    header=text.split("&END",1)
    if len(header)!=2:
        header=re.split(r"(?i)\n\s*/\s*\n",text,maxsplit=1)
    if len(header)!=2:raise ValueError("FCIDUMP header terminator absent")
    meta=header[0]
    def get(key):
        m=re.search(r"\b"+key+r"\s*=\s*(\d+)",meta,re.I)
        if not m:raise ValueError("missing FCIDUMP "+key)
        return int(m.group(1))
    n=get("NORB");ne=get("NELEC");ms=get("MS2")
    if n<1 or ne<0 or ne>2*n or (ne+ms)%2 or (ne-ms)%2:
        raise ValueError("inconsistent particle/spin sector")
    na=(ne+ms)//2;nb=(ne-ms)//2
    if not 0<=na<=n or not 0<=nb<=n:raise ValueError("invalid spin sector")
    h=np.zeros((n,n));eri=np.zeros((n,n,n,n));ecore=0.
    for raw in header[1].splitlines():
        line=raw.strip().split("!")[0]
        if not line:continue
        parts=line.split()
        if len(parts)!=5:continue
        val=float(parts[0].replace("D","E").replace("d","e"))
        p,q,r,s=map(int,parts[1:])
        if p==q==r==s==0:
            ecore=val
        elif r==s==0:
            if not 1<=p<=n or not 1<=q<=n:raise ValueError("orbital index")
            h[p-1,q-1]=h[q-1,p-1]=val
        else:
            if min(p,q,r,s)<1 or max(p,q,r,s)>n:raise ValueError("orbital index")
            p-=1;q-=1;r-=1;s-=1
            for a,b,c,d in {(p,q,r,s),(q,p,r,s),(p,q,s,r),(q,p,s,r),
                              (r,s,p,q),(s,r,p,q),(r,s,q,p),(s,r,q,p)}:
                eri[a,b,c,d]=val
    return h,eri,na,nb,ecore

def apply_ops(state,operations):
    phase=1
    for index,create in operations:
        occupied=(state>>index)&1
        if (create and occupied) or (not create and not occupied):return None,0
        if (state&((1<<index)-1)).bit_count()%2:phase=-phase
        state=state|(1<<index) if create else state&~(1<<index)
    return state,phase

def sector(n,na,nb):
    def masks(k):
        for indexes in itertools.combinations(range(n),k):
            yield sum(1<<i for i in indexes)
    return [a|(b<<n) for a in masks(na) for b in masks(nb)]

def fci_matrix(h,eri,na,nb,ecore=0.,threshold=1e-12):
    n=h.shape[0]
    if h.shape!=(n,n) or eri.shape!=(n,n,n,n):
        raise ValueError("integral tensor shape mismatch")
    if not np.allclose(h,h.T,atol=1e-10) or not np.allclose(eri,eri.transpose(1,0,2,3),atol=1e-10):
        raise ValueError("integral symmetry violated")
    states=sector(n,na,nb)
    lookup={x:i for i,x in enumerate(states)}
    H=np.eye(len(states))*ecore
    # h[p,q] a†_{pσ} a_{qσ}
    one=[(p+spin*n,q+spin*n,v) for spin in (0,1)
         for p in range(n) for q in range(n)
         if abs(v:=h[p,q])>threshold]
    # 1/2 (pq|rs) a†_{pσ} a†_{rτ} a_{sτ} a_{qσ}
    two=[(p+spin*n,q+spin*n,r+other*n,s+other*n,.5*v)
         for spin in (0,1) for other in (0,1)
         for p in range(n) for q in range(n)
         for r in range(n) for s in range(n)
         if abs(v:=eri[p,q,r,s])>threshold]
    for col,state in enumerate(states):
        for p,q,v in one:
            target,phase=apply_ops(state,((q,False),(p,True)))
            if target is not None and target in lookup:H[lookup[target],col]+=v*phase
        for p,q,r,s,v in two:
            target,phase=apply_ops(state,((q,False),(s,False),(r,True),(p,True)))
            if target is not None and target in lookup:H[lookup[target],col]+=v*phase
    if not np.allclose(H,H.T,atol=1e-10):
        raise ValueError("Hamiltonian not Hermitian")
    return H,states

def slater_amplitudes(alpha,beta,states):
    n=alpha.shape[0];na=alpha.shape[1];nb=beta.shape[1]
    if beta.shape[0]!=n:raise ValueError("spin orbital mismatch")
    coeff=[]
    for state in states:
        occupied_a=[i for i in range(n) if state&(1<<i)]
        occupied_b=[i for i in range(n) if state&(1<<(n+i))]
        if len(occupied_a)!=na or len(occupied_b)!=nb:
            raise ValueError("state particle number")
        coeff.append(np.linalg.det(alpha[occupied_a,:])*np.linalg.det(beta[occupied_b,:]))
    return np.array(coeff)

def hubbard_fixture():
    h=np.array([[0.,-1.],[-1.,0.]])
    eri=np.zeros((2,2,2,2))
    eri[0,0,0,0]=eri[1,1,1,1]=4.
    return h,eri,1,1,0.

def run(path=None):
    h,eri,na,nb,ecore=parse_fcidump(path) if path else hubbard_fixture()
    H,states=fci_matrix(h,eri,na,nb,ecore)
    energy=np.linalg.eigvalsh(H)
    result={"scope":"exact small-orbital FCI from supplied physical integrals",
            "source":str(path) if path else "synthetic Hubbard fixture",
            "orbitals":int(len(h)),"alpha":na,"beta":nb,
            "sector_dimension":len(states),"ground_energy_hartree":float(energy[0]),
            "hermiticity_residual":float(np.linalg.norm(H-H.T))}
    if path is None:
        assert abs(energy[0]-(-2*np.sqrt(2)+2))<1e-12
    return result

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--fcidump")
    a=p.parse_args()
    print(json.dumps(run(a.fcidump),indent=2))
