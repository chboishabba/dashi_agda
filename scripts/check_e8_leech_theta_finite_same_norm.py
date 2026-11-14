#!/usr/bin/env python3
"""Exact finite E8/Leech theta coefficient and zeta convolution witness.

E8 is defined as D8 union its half-shifted even-coordinate coset. Counts
are computed from the exact same norm-2n lattice condition as the E8 theta
series, not fabricated from the known Eisenstein formula.

Leech coefficient predictions use the exact modular-form formal polynomial
E4^3 - 720 Delta. They do NOT enumerate Leech vectors or prove lattice
theta identity. Riemann/Epstein zeta correspondence is tested by the
finite multiplicative divisor sum, without asserting infinite convergence.
"""
from __future__ import annotations
from collections import defaultdict
import argparse
import json
from pathlib import Path

def integer_e8_shell_counts(n_max: int):
    """Count norm^2=2n in D8 ∪ (D8+(1/2)^8), exact integer arithmetic."""
    if type(n_max) is not int or n_max<0:
        raise ValueError("nonnegative shell bound required")
    limit=8*n_max # q=4*||v||^2; for ||v||^2=2n, q=8n
    sums=[0]*(n_max+1)
    for half_shift in (False,True):
        # Track (4||v||^2, parity of integer coset coordinates).
        # Half coset requires sum(m_i) even for v_i=m_i+1/2.
        dp={(0,0):1}
        bound=limit+1
        root=int(bound**.5)+1
        modes=[]
        for m in range(-root,root+1):
            contribution=(2*m+1)**2 if half_shift else 4*m*m
            if contribution<=limit:modes.append((m,contribution))
        for _ in range(8):
            nxt=defaultdict(int)
            for (q,parity),mult in dp.items():
                for m,cost in modes:
                    if q+cost<=limit:
                        nxt[(q+cost,(parity+m)%2)]+=mult
            dp=nxt
        for n in range(n_max+1):
            sums[n]+=dp.get((8*n,0),0)
    return sums

def sigma_power(n,k):
    if n<1 or k<0:raise ValueError("positive n and nonnegative power")
    return sum(d**k for d in range(1,n+1) if n%d==0)

def eisenstein_e4(n_max):
    return [1]+[240*sigma_power(n,3) for n in range(1,n_max+1)]

def truncated_mul(a,b,n_max):
    output=[0]*(n_max+1)
    for i,x in enumerate(a):
        if i>n_max:break
        for j,y in enumerate(b):
            if i+j>n_max:break
            output[i+j]+=x*y
    return output

def delta_modular_coefficients(n_max):
    # Delta=q * Product_{n>=1}(1-q^n)^24.
    # Factors with n>n_max never affect degree <=n_max.
    polynomial=[1]+[0]*n_max
    for n in range(1,n_max+1):
        factor=[1]+[0]*n_max
        factor[n]=-1
        for _ in range(24):
            polynomial=truncated_mul(polynomial,factor,n_max)
    return [0]+polynomial[:n_max]

def leech_modular_prediction(n_max):
    e4=eisenstein_e4(n_max)
    cube=truncated_mul(truncated_mul(e4,e4,n_max),e4,n_max)
    delta=delta_modular_coefficients(n_max)
    return [cube[i]-720*delta[i] for i in range(n_max+1)]

def check(n_max):
    shell=integer_e8_shell_counts(n_max)
    e4=eisenstein_e4(n_max)
    leech=leech_modular_prediction(n_max)
    if shell!=e4:
        first=next(i for i in range(n_max+1) if shell[i]!=e4[i])
        raise AssertionError(f"original E8 shell mismatch at norm-2n index {first}")
    # The finite Dirichlet product coefficient is sigma_3(n)=sum_{d|n}d^3.
    if any((shell[n]//240)!=sigma_power(n,3) for n in range(1,n_max+1)):
        raise AssertionError("finite E8 zeta coefficient mismatch")
    if n_max>=2 and (leech[0]!=1 or leech[1]!=0 or leech[2]!=196560):
        raise AssertionError("Leech modular candidate failed q^1/q^2 check")
    return {
        "kind":"e8_original_coset_finite_theta_and_leech_modular_candidate",
        "schema":1,"norm_convention":"E8 norm^2=2n; theta q^n",
        "shell_bound":n_max,
        "e8_shell_counts_exact":shell,
        "e4_coefficients_exact":e4,
        "e8_e4_equal_through_bound":True,
        "e8_finite_zeta_dirichlet_coefficients":[
            {"n":n,"e8_shell":shell[n],"sigma3":sigma_power(n,3)}
            for n in range(1,n_max+1)],
        "e8_zeta_formula_target":"240*2^(-s)*zeta(s)*zeta(s-3) for Re(s)>4",
        "leech_modular_candidate_coefficients":leech,
        "leech_modular_q1_zero":n_max>=1 and leech[1]==0,
        "leech_modular_q2_196560":n_max>=2 and leech[2]==196560,
        "leech_rootless_actual_lattice_enumerated":False,
        "theta_e8_equals_e4_all_coefficients_proved":False,
        "theta_leech_equals_modular_candidate_all_coefficients_proved":False,
        "mellin_absolute_convergence_proved":False,
        "original_model_lila_representation_weld_proved":False,
        "note":"Exact finite coefficient witness, not a general modular-form/lattice theta proof."}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--max-shell",type=int,default=5)
    p.add_argument("--output",type=Path)
    a=p.parse_args()
    report=check(a.max_shell)
    out=json.dumps(report,sort_keys=True,indent=2)+"\n"
    if a.output:
        if a.output.exists():raise FileExistsError("refuse overwrite original witness")
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(out)
    print(out,end="")
if __name__=="__main__":main()
