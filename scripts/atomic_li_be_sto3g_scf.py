#!/usr/bin/env python3
"""Self-contained Li/Be minimal-basis UHF/RHF producer.

Attribution / role separation:
- Basis data: STO-3G values from the Basis Set Exchange / Hehre-Stewart-Pople
  lineage.  The basis source supplies orbital basis parameters only.
- DASHI owns the implementation below: same-centre normalized s-Gaussian
  overlap, kinetic, nuclear-attraction and electron-repulsion integrals plus
  generalized-eigenvalue UHF/RHF iteration.
- This is a minimal-basis execution receipt for simultaneous 1s/2s state
  tracking.  It is not complete-basis convergence, correlation, relativity,
  measured spectroscopy, or a ternary-to-atom identification.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

C1=np.array([0.15432897,0.53532814,0.44463454])
C2=np.array([-0.09996723,0.39951283,0.70011547])
DATA={
 "Li":{"Z":3,"exps":[np.array([16.1195750,2.9362007,0.7946505]),np.array([0.6362897,0.1478601,0.0480887])],"coeffs":[C1,C2],"occ":(2,1)},
 "Be":{"Z":4,"exps":[np.array([30.1678710,5.4951153,1.4871927]),np.array([1.3148331,0.3055389,0.0993707])],"coeffs":[C1,C2],"occ":(2,2)},
}

def norm(a): return (2*a/math.pi)**0.75

def overlap0(a,b):
    p=a+b
    return norm(a)*norm(b)*(math.pi/p)**1.5

def kinetic0(a,b):
    return overlap0(a,b)*3*a*b/(a+b)

def nuclear0(a,b,Z):
    return -Z*norm(a)*norm(b)*2*math.pi/(a+b)

def eri0(a,b,c,d):
    p=a+b; q=c+d
    return norm(a)*norm(b)*norm(c)*norm(d)*2*math.pi**2.5/(p*q*math.sqrt(p+q))

def build(atom):
    d=DATA[atom]; Z=d['Z']; exps=d['exps']; coeffs=d['coeffs']; nb=2
    S=np.zeros((nb,nb)); h=np.zeros((nb,nb)); eri=np.zeros((nb,nb,nb,nb))
    for m in range(nb):
      for n in range(nb):
        for a,ca in zip(exps[m],coeffs[m]):
          for b,cb in zip(exps[n],coeffs[n]):
            S[m,n]+=ca*cb*overlap0(a,b)
            h[m,n]+=ca*cb*(kinetic0(a,b)+nuclear0(a,b,Z))
        for l in range(nb):
          for s in range(nb):
            eri[m,n,l,s]=sum(ca*cb*cc*cd*eri0(a,b,c,e)
              for a,ca in zip(exps[m],coeffs[m])
              for b,cb in zip(exps[n],coeffs[n])
              for c,cc in zip(exps[l],coeffs[l])
              for e,cd in zip(exps[s],coeffs[s]))
    return S,h,eri

def solve(F,S):
    ev,U=np.linalg.eigh(S)
    X=U@np.diag(ev**-0.5)@U.T
    e,Cp=np.linalg.eigh(X.T@F@X)
    return e,X@Cp

def uhf(atom):
    S,h,eri=build(atom); na,nb=DATA[atom]['occ']
    _,C=solve(h,S)
    Pa=C[:,:na]@C[:,:na].T; Pb=C[:,:nb]@C[:,:nb].T
    old=1e100
    for it in range(200):
        P=Pa+Pb
        J=np.einsum('ls,mnls->mn',P,eri)
        Ka=np.einsum('ls,mlns->mn',Pa,eri)
        Kb=np.einsum('ls,mlns->mn',Pb,eri)
        ea,Ca=solve(h+J-Ka,S); eb,Cb=solve(h+J-Kb,S)
        Pan=Ca[:,:na]@Ca[:,:na].T; Pbn=Cb[:,:nb]@Cb[:,:nb].T
        Pn=Pan+Pbn
        Jn=np.einsum('ls,mnls->mn',Pn,eri)
        Kan=np.einsum('ls,mlns->mn',Pan,eri)
        Kbn=np.einsum('ls,mlns->mn',Pbn,eri)
        E=np.einsum('mn,mn',Pn,h)+0.5*(np.einsum('mn,mn',Pn,Jn)-np.einsum('mn,mn',Pan,Kan)-np.einsum('mn,mn',Pbn,Kbn))
        delta=max(np.max(abs(Pan-Pa)),np.max(abs(Pbn-Pb)))
        Pa,Pb=Pan,Pbn
        if delta<1e-11 and abs(E-old)<1e-11: break
        old=E
    return E,ea,eb,Ca,Cb,it+1

def basis_value(atom,mu,r):
    d=DATA[atom]
    return sum(c*norm(a)*np.exp(-a*r*r) for a,c in zip(d['exps'][mu],d['coeffs'][mu]))

def run(out):
    out=Path(out); out.mkdir(parents=True,exist_ok=True)
    receipt={'basis_source':{
        'name':'STO-3G',
        'authority':'Basis Set Exchange / Hehre-Stewart-Pople lineage',
        'role':'explicit Gaussian orbital basis parameters only',
        'promotion':'does not validate DASHI mechanism or guarantee basis convergence'},
        'method':{
        'name':'same-centre Gaussian UHF/RHF',
        'boundary':'minimal s-only Li/Be 1s/2s state tracking; no correlation/relativity/complete-basis claim'}}
    results={}
    for atom in ('Li','Be'):
        E,ea,eb,Ca,Cb,it=uhf(atom)
        results[atom]=(E,ea,eb,Ca,Cb,it)
        receipt[atom]={'energy_hartree':float(E),'iterations':it,'alpha_orbital_energies':ea.tolist(),'beta_orbital_energies':eb.tolist()}
        r=np.linspace(0,12,1200)
        fig,ax=plt.subplots(figsize=(9,6))
        na,nb=DATA[atom]['occ']
        for i in range(na):
            psi=sum(Ca[mu,i]*basis_value(atom,mu,r) for mu in range(2))
            ax.plot(r,4*math.pi*r*r*np.abs(psi)**2,label=f'alpha MO {i+1}, eps={ea[i]:.4f} Eh')
        if atom=='Li':
            psi=sum(Cb[mu,0]*basis_value(atom,mu,r) for mu in range(2))
            ax.plot(r,4*math.pi*r*r*np.abs(psi)**2,label=f'beta MO 1, eps={eb[0]:.4f} Eh')
        ax.set_xlabel('r / a0'); ax.set_ylabel('4 pi r^2 |psi(r)|^2')
        ax.set_title(f'{atom} STO-3G self-consistent occupied s-orbitals')
        ax.legend(); ax.grid(alpha=.2)
        fig.savefig(out/f'{atom.lower()}_sto3g_scf_radial_orbitals.png',dpi=220,bbox_inches='tight'); plt.close(fig)
    (out/'li_be_sto3g_scf_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

def main():
    p=argparse.ArgumentParser(); p.add_argument('--out',default='outputs/atomic_li_be_sto3g')
    args=p.parse_args(); print(json.dumps(run(args.out),indent=2))

if __name__=='__main__': main()
