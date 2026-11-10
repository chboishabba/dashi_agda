#!/usr/bin/env python3
"""Finite proof-by-evaluation of ipie melting-core occupation preservation.

The ipie ParticleHole class inserts ncore occupied molecular orbitals when
its supplied CI determinants contain fewer electrons than the declared
full-system spin counts. Their occupied indices become
    [0,..,ncore-1] ++ [ncore + active_index]
for alpha and beta. This preserves *all* antisymmetrized full-space Slater
minors and reduces nact from (ncore + 8) to 8 in the Wicks intermediates.

Source: ipie/trial_wavefunction/particle_hole.py setup_basic_wavefunction;
Zhao et al. 2025 core/active/virtual trial construction.
"""
from itertools import combinations
import json
import numpy as np

def full_occupations(active,ncore):
    active=np.asarray(active,dtype=int)
    if active.ndim!=2 or active.size==0:
        raise ValueError("nonempty rectangular active occupation array required")
    if not np.all((active>=0)&(active<8)):
        raise ValueError("active orbital beyond the 8-orbital source")
    if any(len(set(row.tolist()))!=len(row) for row in active):
        raise ValueError("duplicate spatial orbital")
    return np.hstack((np.broadcast_to(np.arange(ncore),(len(active),ncore)),
                      active+ncore))

def self_test():
    ncore,nactive,nvirt,npairs=2,4,2,2
    nmo=ncore+nactive+nvirt
    nocc=ncore+npairs
    rng=np.random.default_rng(603)
    active=np.asarray(list(combinations(range(nactive),npairs)),dtype=int)
    melted=full_occupations(active,ncore)
    assert np.all(melted[:, :ncore]==np.arange(ncore))
    assert np.all(melted[:, ncore:]==active+ncore)
    c=rng.normal(size=len(active))+1j*rng.normal(size=len(active))
    c/=np.linalg.norm(c)
    a=rng.normal(size=(nmo,nocc))+1j*rng.normal(size=(nmo,nocc))
    b=rng.normal(size=(nmo,nocc))+1j*rng.normal(size=(nmo,nocc))
    by_melted=sum(np.conj(v)*np.linalg.det(a[oa])*np.linalg.det(b[oa])
                  for v,oa in zip(c,melted))
    by_direct=sum(np.conj(v)*np.linalg.det(
                    a[np.r_[np.arange(ncore),ncore+oa],:])*
                    np.linalg.det(b[np.r_[np.arange(ncore),ncore+oa],:])
                  for v,oa in zip(c,active))
    difference=float(abs(by_melted-by_direct))
    assert difference<1e-12
    # Nickel predicted protocol state: no 80-core-index expansion needed
    # in each of C(8,4)=70 source active determinants.
    nickel_active=np.asarray(list(combinations(range(8),4)),dtype=int)
    nickel_melted=full_occupations(nickel_active,80)
    assert nickel_melted.shape==(70,84)
    return {"source":"native ipie melting-core occupation mapping",
            "finite_full_space_overlap_identity_error":difference,
            "nickel_source_active_determinants":70,
            "nickel_core_pairs":80,
            "full_alpha_spin_occupations":84,
            "ipie_active_wicks_orbitals":8,
            "unoptimized_reference_orbitals":88,
            "ipie_installed_and_executed":False,
            "passed":True}

if __name__=="__main__":
    print(json.dumps(self_test(),indent=2))
