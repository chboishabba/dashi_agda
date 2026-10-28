#!/usr/bin/env python3
"""Cross-PR 9999!/pi/e^i boundary for actual DASHI horned 2I source.

Reuses existing:
  alexander_horned_c3_finite_SU2_gauge_simulator.build, comm, powq
  DASHI.Mathematics.Topology.AlexanderHornedAbelianHolonomyBIDIExact
    [source Agda theorem: all meridian-generated abelian characters trivial]
  DASHI Pickover PR #1260 [independent real phase / CRT source]
No unmerged Pickover Python code is vendored or imported into this branch.

Alexander (1924), Hatcher Ex.2B.2 are original wild topology sources;
Hamilton/Klein own quaternion and binary icosahedral background;
Euler/de Moivre, Lindemann (1882)/Weierstrass (1885) own complex phase
and transcendence. Our finite tests are not their original discoveries.
"""
from math import factorial

from alexander_horned_c3_finite_SU2_gauge_simulator import (
    ID, NEG, build, comm, mul, powq,
)

def run():
    group,q,comm_section,rootpair=build()
    assert len(group)==len(comm_section)==120
    assert set(group)==set(comm_section)
    assert all(comm(*comm_section[g])==g for g in group)
    # Every element of 2I is a single commutator, so [2I,2I]=2I.
    # Therefore any group homomorphism 2I -> any abelian group is
    # identically neutral. This is an exact finite source witness.
    assert powq(q,3)==NEG and powq(q,6)==ID
    assert mul(NEG,NEG)==ID and NEG!=ID
    # q^3=-I_2 has normalized SU2 halftrace -1. This is NOT
    # the value of a compatible U(1) character on the perfect group.
    assert NEG[0][0]==-1 and NEG[0][1]==0
    assert all(x==(0,0) for x in NEG[1:])

    # Exactly recompute the mathematical congruence from Pickover #1260.
    # This is a 1-line independent CRT cross-check, not an imported
    # implementation or a real-angle/holonomy identification.
    E=factorial(9999)
    residue=pow(99,E,9999)
    assert residue==4950 and pow(residue,2,9999)==residue
    assert tuple(residue%d for d in (9,11,101))==(0,0,1)
    assert pow(99,E,3)==0

    # Every C3 scalar character chi_j, j=0,1,2, sends the chosen
    # external rotation R^N to 1 when N is divisible by 3.
    # This says nothing about e^(iN), whose angle is measured in
    # radians, and nothing about the nonabelian SU2 matrix rho(q).
    for j in (0,1,2):
        assert j*pow(99,E,3)%3==0

    # On three two-dimensional channels the block 3-cycle permutes
    # the six basis vectors as two 3-cycles, hence determinant +1.
    # This determinant is NOT an arbitrary nontrivial orbifold C3
    # character, though such characters exist.
    perm=(2,3,4,5,0,1)
    inversions=sum(perm[i]>perm[k] for i in range(6) for k in range(i+1,6))
    assert inversions%2==0
    print('PASS actual 120-element binary-icosahedral commutator section')
    print('PASS 2I perfect -> every scalar abelian character is trivial')
    print('PASS source q^3=-I2: nonabelian halftrace -1, not scalar holonomy')
    print('PASS Pickover 9999! finite CRT residue 4950 with mu3 projection 1')
    print('PASS two 3-cycles give det +1 for U(6) C3 channel permutation')
    print('BOUNDARY: e^(i 99^(9999!)) is a REAL-angle phase, not a mu9999 or SU2 value')
    print('BOUNDARY: actual geometric pi1/group-map and physical gauge data are separate')

if __name__=='__main__':
    run()
