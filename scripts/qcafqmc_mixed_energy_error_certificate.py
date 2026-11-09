#!/usr/bin/env python3
"""Certified finite-state NQS mixed-energy error transport.

For ideal state psi and learned state theta on the SAME finite Hilbert space,
D=<psi|w>, N=<psi|H w>; learned quantities are D', N'. Given
|D'-D|<=d and |N'-N|<=n and |D|>d, the exact identity

  N'/D' - N/D = ((N'-N)*D - N*(D'-D))/(D*D')

gives |delta E| <= (n*|D|+|N|*d)/(|D|*(|D|-d)).

Bounds may be estimated from a state 2-norm error by Cauchy-Schwarz, with
d=||theta-psi||*||w|| and n=||theta-psi||*||H w||.
No statistical generalization, phaseless bias bound, or source data is assumed.

Attribution: standard ratio perturbation and Cauchy-Schwarz inequalities;
motivated by Provazza, Knitter et al., arXiv:2611.08129 (2026).
"""
import argparse
import json
import numpy as np

class UncertifiableOverlap(ValueError):
    pass

def energy_certificate(H, psi, learned, walker, tolerance=1.e-12):
    H=np.asarray(H,dtype=np.complex128)
    psi=np.asarray(psi,dtype=np.complex128)
    learned=np.asarray(learned,dtype=np.complex128)
    walker=np.asarray(walker,dtype=np.complex128)
    n=psi.size
    if psi.shape!=(n,) or learned.shape!=(n,) or walker.shape!=(n,) or H.shape!=(n,n):
        raise ValueError("mismatched Hilbert-space dimensions")
    for array in (H,psi,learned,walker):
        if not np.isfinite(array).all():raise ValueError("nonfinite quantum-state data")
    if not np.allclose(H,H.conj().T,atol=tolerance,rtol=0):
        raise ValueError("H is not Hermitian")
    denominator=np.vdot(psi,walker)
    learned_denominator=np.vdot(learned,walker)
    numerator=np.vdot(psi,H@walker)
    learned_numerator=np.vdot(learned,H@walker)
    eta=np.linalg.norm(learned-psi)
    d=float(eta*np.linalg.norm(walker))
    m=float(eta*np.linalg.norm(H@walker))
    absolute_denominator=float(abs(denominator))
    if absolute_denominator <= d + tolerance:
        raise UncertifiableOverlap("trial-state error can cross an overlap node")
    bound=float((m*absolute_denominator+abs(numerator)*d)/
                (absolute_denominator*(absolute_denominator-d)))
    difference=float(abs(learned_numerator/learned_denominator-
                         numerator/denominator))
    if difference > bound+max(1e-10,1e-9*bound):
        raise AssertionError("mixed-energy error exceeds Cauchy-Schwarz certificate")
    return {"exact_mixed_energy_real":float((numerator/denominator).real),
            "exact_mixed_energy_imag":float((numerator/denominator).imag),
            "learned_mixed_energy_real":float((learned_numerator/learned_denominator).real),
            "learned_mixed_energy_imag":float((learned_numerator/learned_denominator).imag),
            "state_2norm_error":float(eta),
            "certified_denominator_error":d,
            "certified_numerator_error":m,
            "ideal_overlap_modulus":absolute_denominator,
            "guaranteed_energy_error_upper_bound":bound,
            "observed_energy_error":difference,
            "condition_is_satisfied":True}

def self_test():
    H=np.array([[1,.2,0],[.2,2,.1],[0,.1,3]],dtype=complex)
    psi=np.array([1,1j,.7],dtype=complex)
    psi/=np.linalg.norm(psi)
    learned=psi+np.array([1e-4,-2e-4j,3e-4])
    walker=np.array([.8,.25j,.4],dtype=complex)
    control=energy_certificate(H,psi,learned,walker)
    assert control["observed_energy_error"] <= control["guaranteed_energy_error_upper_bound"]
    node=np.array([0,1,0],dtype=complex)
    exact=np.array([1,0,0],dtype=complex)
    approximate=np.array([1,1e-3,0],dtype=complex)
    try:
        energy_certificate(H,exact,approximate,node)
    except UncertifiableOverlap:
        node_rejected=True
    else:
        raise AssertionError("node negative control was incorrectly accepted")
    assert node_rejected
    return {"positive_certificate":control,"near_node_rejected":node_rejected}

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if not args.self_test:parser.error("use --self-test or import energy_certificate")
    print(json.dumps(self_test(),indent=2))
