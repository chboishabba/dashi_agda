#!/usr/bin/env python3
"""Exact finite VCE core/active embedding regression.

Verifies the mathematical boundary of Zhao et al., arXiv:2506.22408
Eq. (30): core determinant ⊗ active CI trial ⊗ virtual vacuum.

When a walker is block-separated, its full-space overlap is the ordinary
active-space CI overlap. When core and active walker orbitals mix, the
naive active-only overlap fails; the full-space Slater minors remain correct.
This is a *finite algebraic test*, not a proof of a scalable VCE Pfaffian
implementation, of AFQMC convergence, or of nickel input identity.
"""
import itertools
import json
import numpy as np

def active_space_overlap(coefficients,occupations,alpha,beta):
    total=0j
    for coefficient,occ in zip(coefficients,occupations):
        rows=list(occ)
        total+=np.conj(coefficient)*np.linalg.det(alpha[rows,:])*np.linalg.det(beta[rows,:])
    return total

def full_space_core_active_overlap(coefficients,occupations,alpha,beta,ncore):
    total=0j
    for coefficient,occ in zip(coefficients,occupations):
        rows=list(range(ncore))+[ncore+i for i in occ]
        total+=np.conj(coefficient)*np.linalg.det(alpha[rows,:])*np.linalg.det(beta[rows,:])
    return total

def validate():
    rng=np.random.default_rng(100)
    ncore,nactive,nvirt,npairs=2,4,2,2
    nmo=ncore+nactive+nvirt
    occupations=list(itertools.combinations(range(nactive),npairs))
    coefficients=rng.normal(size=len(occupations))+1j*rng.normal(size=len(occupations))
    coefficients/=np.linalg.norm(coefficients)
    alpha_active=rng.normal(size=(nactive,npairs))+1j*rng.normal(size=(nactive,npairs))
    beta_active=rng.normal(size=(nactive,npairs))+1j*rng.normal(size=(nactive,npairs))
    alpha=np.zeros((nmo,ncore+npairs),dtype=complex)
    beta=np.zeros_like(alpha)
    alpha[:ncore,:ncore]=np.eye(ncore)
    beta[:ncore,:ncore]=np.eye(ncore)
    alpha[ncore:ncore+nactive,ncore:]=alpha_active
    beta[ncore:ncore+nactive,ncore:]=beta_active
    on_active=active_space_overlap(coefficients,occupations,alpha_active,beta_active)
    on_full=full_space_core_active_overlap(coefficients,occupations,alpha,beta,ncore)
    assert abs(on_active-on_full)<1e-12

    # This is a substantive negative control: mixing the occupied-core
    # and active-orbital rows contributes additional minors.
    mixed_alpha=alpha.copy()
    mixed_beta=beta.copy()
    mixed_alpha[ncore,0]=.3
    mixed_alpha[0,ncore]=.23
    mixed_beta[ncore+1,1]=.4
    mixed_beta[1,ncore+1]=.17
    mixed=full_space_core_active_overlap(coefficients,occupations,
                                         mixed_alpha,mixed_beta,ncore)
    failure=abs(mixed-on_active)
    assert failure>.01
    return {
      "scope":"finite core-active-virtual trial embedding",
      "core_doubly_occupied":ncore,"active_orbitals":nactive,
      "virtual_orbitals":nvirt,"active_pairs":npairs,
      "number_of_active_paired_determinants":len(occupations),
      "block_separated_overlap_error":float(abs(on_active-on_full)),
      "naive_active_overlap_failure_under_core_mixing":float(failure),
      "passed":True,
      "original_ionq_orbitals_verified":False
    }

if __name__=="__main__":
    print(json.dumps(validate(),indent=2))
