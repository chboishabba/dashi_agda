#!/usr/bin/env python3
"""Constructive H4-zeta Fourier intertwiner (not Monster or D4 recognition).

Source: PR #1148's selected 4-pair Heisenberg H4 and 10-marker regular action.
Target: already-owned PR #1098 / #1162 six-pair Schr F3^6, restricted to
first four Heisenberg pairs. Original mathematical Fourier sources:
Serre 1977; Terras 1999; Stone-von Neumann finite Heisenberg theory.

For |a,b>_zeta, left H4 acts as
 lambda(A,B,C)|a,b> = zeta^(C+B.a)|a+A,b+B>.
For each eta in F3^4 define
 |x,eta> = sum_b zeta^(eta.b)|x+eta,b>_zeta.
Then lambda(A,B,C)|x,eta> = zeta^(C+B.x)|x+A,eta>.
The inverse has coefficient 1/81 via exact 81-point Fourier
orthogonality. This is an H4-module equivalence ONLY.
"""
import itertools,json
from collections import Counter
V=list(itertools.product(range(3),repeat=4))
Z=(0,0,0,0)
def dot(x,y):return sum(a*b for a,b in zip(x,y))%3
def add(x,y):return tuple((a+b)%3 for a,b in zip(x,y))
def sub(x,y):return tuple((a-b)%3 for a,b in zip(x,y))
def audit():
    counts=Counter()
    for b in V:
        for d in V:
            hist=tuple(sum(dot(eta,sub(b,d))==k for eta in V) for k in range(3))
            assert hist==((81,0,0) if b==d else (27,27,27))
            counts['diagonal' if b==d else 'off_diagonal']+=1
    assert counts=={'diagonal':81,'off_diagonal':6480}
    generators=[(Z,Z,1)]
    for i in range(4):
        e=tuple(int(i==j) for j in range(4))
        generators.extend(((e,Z,0),(Z,e,0)))
    tested=0
    for x in V:
        for eta in V:
            a=add(x,eta)
            for A,B,C in generators:
                assert (C+dot(B,a)-dot(eta,B))%3==(C+dot(B,x))%3
                assert sub(add(a,A),eta)==add(x,A)
                tested+=1
    assert tested==59049
    slots=set()
    for marker in range(10):
        for e in range(81):
            slot=marker*81+e
            j,u=divmod(slot,9)
            assert 0<=j<90 and 0<=u<9
            assert divmod(j*9+u,81)==(marker,e)
            slots.add((j,u))
    assert len(slots)==810
    return {
      'schema':'jfine-regular-H4-zeta-to-SchrH6-restricted-Fourier-v1',
      'source_phase_dimension':10*3**8,
      'target_phase_dimension':90*3**6,
      'H4_Schrodinger_degree':81,
      'H6_Schrodinger_degree':729,
      'source_regular_H4_zeta_copy_count':10*81,
      'target_H6_Schrodinger_restricted_H4_copy_count':90*9,
      'exact_fourier_gram_pairs':6561,
      'DFT81_diagonal_pairs':counts['diagonal'],
      'DFT81_off_diagonal_pairs':counts['off_diagonal'],
      'source_to_Schrodinger_intertwiner_generator_checks':tested,
      'explicit_H4_multiplicity_slot_bijection':810,
      'actual_H4_subgroup_of_Monster_E_identified':False,
      'D4_normalizer_intertwiner':False,
      'same_object_Monster_Wzeta_linear_recognition':False,
      'Agda_kernel_verified':False
    }
if __name__=='__main__':print(json.dumps(audit(),indent=2,sort_keys=True))
