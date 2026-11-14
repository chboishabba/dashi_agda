#!/usr/bin/env python3
"""Exact cyclotomic 3x3 finite Fourier max-cut receipt.

Character values live in Z[omega] with omega^2+omega+1=0,
represented by integer pairs (a,b) = a+b*omega. This checks exact
orthogonality, shift eigenphase, Parseval, Fourier inversion and
convolution on G=(Z/3Z)^2. Physical NS mode pairs and Balaban YM 3x3
block indices are *different* carriers: this provides only a common
finite character calculation, NOT a physical source-state intertwiner,
interacting RG convergence, a quantum unitary realization or NS
regularity. There is no floating-point sine approximation here.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

ZERO=(0,0)
ONE=(1,0)
OMEGA=(0,1)
OMEGA2=(-1,-1)
GROUP=tuple((x,y) for x in range(3) for y in range(3))

def plus(a,b):
    return (a[0]+b[0],a[1]+b[1])

def minus(a,b):
    return (a[0]-b[0],a[1]-b[1])

def times(a,b):
    # omega^2=-1-omega
    x,y=a
    u,v=b
    return (x*u-y*v,x*v+y*u-y*v)

def scalar(n,a):
    return (n*a[0],n*a[1])

def conj(a):
    # bar(omega)=omega^2=-1-omega
    return (a[0]-a[1],-a[1])

def omega_pow(k):
    return (ONE,OMEGA,OMEGA2)[k%3]

def add_g(a,b):
    return ((a[0]+b[0])%3,(a[1]+b[1])%3)

def neg_g(a):
    return ((-a[0])%3,(-a[1])%3)

def character(k,x):
    return omega_pow(k[0]*x[0]+k[1]*x[1])

def total(values):
    out=ZERO
    for v in values:out=plus(out,v)
    return out

def transform(f):
    # unnormalised Fourier sum F(k)=sum_x f(x)*bar(chi_k(x))
    return {k:total(times(f[x],conj(character(k,x))) for x in GROUP)
            for k in GROUP}

def convolution(f,g):
    return {z:total(times(f[x],g[add_g(z,neg_g(x))]) for x in GROUP)
            for z in GROUP}

def exact_receipt():
    # Fully enumerated finite group identities, with exact cyclotomic integers.
    assert all(times(omega_pow(k),omega_pow(l))==omega_pow(k+l)
               for k in range(3) for l in range(3))
    assert plus(plus(ONE,OMEGA),OMEGA2)==ZERO
    assert all(times(character(k,x),character(k,y))==
               character(k,add_g(x,y))
               for k in GROUP for x in GROUP for y in GROUP)
    assert all(total(character(k,x) for x in GROUP)==
               ((9,0) if k==(0,0) else ZERO) for k in GROUP)
    assert all(total(times(character(k,x),conj(character(l,x)))
                         for x in GROUP)==
               ((9,0) if k==l else ZERO)
               for k in GROUP for l in GROUP)
    # Test a nontrivial integer-valued source field pair (not delta-only).
    f={x:(x[0]-x[1]+1,0) for x in GROUP}
    g={x:(2*x[0]+x[1]-2,0) for x in GROUP}
    F=transform(f)
    G=transform(g)
    C=transform(convolution(f,g))
    assert all(C[k]==times(F[k],G[k]) for k in GROUP)
    # Fourier inversion: sum_k F(k) chi_k(x)=9 f(x)
    assert all(total(times(F[k],character(k,x)) for k in GROUP)==
               scalar(9,f[x]) for x in GROUP)
    # Exact Parseval: sum_k F(k)*conj(F(k)) = 9 sum_x f(x)*conj(f(x))
    assert total(times(F[k],conj(F[k])) for k in GROUP)==scalar(
        9,total(times(f[x],conj(f[x])) for x in GROUP))
    # In Fourier coordinates translation is multiplication by a character.
    for t in GROUP:
        shifted={x:f[add_g(x,t)] for x in GROUP}
        shifted_fft=transform(shifted)
        assert all(shifted_fft[k]==times(character(k,t),F[k]) for k in GROUP)
    # High-high frequency k and -k generate zero OUTPUT frequency:
    # source mode addition is not the same as zero INPUT frequency.
    assert all(add_g(k,neg_g(k))==(0,0) for k in GROUP)
    return {
       "kind":"finite_369_c3x3_exact_cyclotomic_character_contract",
       "group":"Z3 x Z3, 9 points",
       "ring":"Z[omega], omega^2+omega+1=0, exact integer pairs",
       "character_homomorphism_729_checks":True,
       "orthogonality_81_checks":True,
       "convolution_9_frequency_checks":True,
       "inverse_9_points":True,
       "parseval_exact":True,
       "translation_eigenphase_81_checks":True,
       "high_high_opposite_output_zero_9_cases":True,
       "source_provenance": [
         "DASHI/Biology/BalancedTernaryFourierModeExact.agda",
         "DASHI/Physics/YangMills/BalabanP33ThreeCycleBlockTorusCrossPollinationExact.agda",
         "DASHI/Physics/Closure/NSTriadKNLuoGalerkinFourierModePairExact.agda",
         "DASHI/Algebra/Quantum/ShorCyclicQFTCarrierTransportExact.agda",
         "DASHI/Wikimedia/IbrahimC3ZetaRegularCharacterOEISQuantumGRBidiExact.agda",
       ],
       "source_carrier_identifications_kernel_proved":False,
       "NS_physical_nonlinearity_estimated":False,
       "YM_Wilson_Rg_estimated":False,
       "atomic_hamiltonian_identified":False,
       "quantum_register_unitarity_this_source_proved":False,
       "Leech_learner_phase_circuit_measured":False,
       "note":"Common exact Fourier algebra only, not a cross-domain physical equivalence."
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    obj=exact_receipt()
    rendered=json.dumps(obj,sort_keys=True,indent=2)+"\n"
    if a.output:
        if a.output.exists():raise FileExistsError("refuse to overwrite source receipt")
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(rendered)
    print(rendered,end="")
if __name__=="__main__":
    main()
