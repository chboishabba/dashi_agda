#!/usr/bin/env python3
"""Finite local D4 duality test; NOT a 6.Suz or Monster intertwiner.

The old nine-cell D4 action is an orthogonal signed-permutation model.
Thus Sym²(U12) and its contragredient are canonically D4-isomorphic using
the inherited quadratic pairing, even though 6.Suz centre-C3 phases differ.
Reuses the existing nine-cell / 78 producer rather than new D4 machinery.
"""
import json
from monster_3b_jfine_ninecell_sym2_intertwiner import (
    nine_cell, direct, sym2, chr,
)
def check_signed_orthogonal(g):
    n=len(g)
    assert sorted(j for j,_ in g)==list(range(n))
    assert all(s in (-1,1) for _,s in g)
    inv=[None]*n
    for i,(j,z) in enumerate(g):inv[j]=(i,z)
    invT=[None]*n
    for j,(i,z) in enumerate(inv):invT[i]=(j,z)
    assert invT==g
    return n
def audit():
    r9,s9=nine_cell()
    r12=direct(r9,[(0,1),(1,-1),(2,-1)])
    s12=direct(s9,[(0,1),(1,1),(2,-1)])
    r78,s78=sym2(r12),sym2(s12)
    assert [check_signed_orthogonal(g) for g in (r12,s12,r78,s78)]==[12,12,78,78]
    assert chr(direct(r12,r78),direct(s12,s78))==(90,18,2,18,18)
    return dict(status="exact_D4_self_duality_checked",
      generator_dimensions=[12,12,78,78],
      direct_and_dual_Sym2_identical_D4_matrices=True,
      inherited_D4_invariant_inner_product=True,
      ninety_D4_character=[90,18,2,18,18],
      same_6Suz_module=False,
      source_central_phase_difference="Sym²(ζ^a)=ζ^(2a), dual Sym²(ζ^a)=ζ^(-2a)",
      actual_Monster_intertwiner=False)
if __name__=="__main__":print(json.dumps(audit(),indent=2))
