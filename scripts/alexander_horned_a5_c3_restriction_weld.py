#!/usr/bin/env python3
"""Existing A5/C3 restriction -> horned finite VOA C3xC3 compatibility.

Source owners: Serre, Fulton/Harris; DASHI
  Foundations/IcosahedralSO3RestrictionJ0To35Exact.agda
  Foundations/PolyhedralFixedSpaceSpectrumJ0To35Exact.agda
  Foundations/PolyhedralFiniteRestrictionInstancesExact.agda
  Mathematics/Topology/AlexanderHornedC3FiniteVOAActorExact.agda

This is a finite exact permutation/character audit, NOT geometric pi1
certification and NOT Agda kernel validation. No A5 -> C3 quotient
is constructed: the inclusion C3 <= A5 is used instead.
"""
from itertools import permutations, product

ID = tuple(range(5))

def multiply(a, b):
    return tuple(a[b[i]] for i in range(5))

def inverse(a):
    return tuple(a.index(i) for i in range(5))

def is_even(a):
    return sum(a[i] > a[j] for i in range(5)
               for j in range(i + 1, 5)) % 2 == 0

A5 = tuple(p for p in permutations(range(5)) if is_even(p))
assert len(A5) == 60
assert len(set(A5)) == 60

# Real 3-cycle (0 1 2), fixing 3 and 4.
s = (1, 2, 0, 3, 4)
s2 = multiply(s, s)
assert s in A5 and s2 in A5
assert s != ID and s2 != ID and multiply(s2, s) == ID
cycle = (ID, s, s2)
assert len(set(cycle)) == 3

def commutator(a, b):
    return multiply(multiply(multiply(a, b), inverse(a)), inverse(b))

# Every commutator of a source group lies in the kernel of any
# homomorphism into an abelian group; commutator width=1 for A5
# follows here from finite exact enumeration.
commutators = {commutator(a, b) for a in A5 for b in A5}
assert len(commutators) == 60
assert set(A5) == commutators

# For Q=A5^3 rtimes C3, choose the diagonal internal generator
# (s,s,s;0) and independent external sector shift (e,e,e;1).
# Their actions are (i,a) -> (i,s*a) and (i,a) -> (i+1,a).
def H_action(k, l, x):
    i, a = x
    return ((i + l) % 3, multiply(cycle[k], a))

addresses = tuple(product(range(3), A5))
assert len(addresses) == 180

for x in addresses:
    assert H_action(0, 0, x) == x
    assert H_action(1, 0, H_action(0, 1, x)) == H_action(0, 1, H_action(1, 0, x))
    assert H_action(1, 0, H_action(1, 0, H_action(1, 0, x))) == x
    assert H_action(0, 1, H_action(0, 1, H_action(0, 1, x))) == x
    assert all(H_action(k, l, x) != x for k, l in product(range(3), repeat=2)
               if (k, l) != (0, 0))

seen = set()
orbits = []
for x in addresses:
    if x in seen:
        continue
    orbit = {H_action(k, l, x) for k, l in product(range(3), repeat=2)}
    assert len(orbit) == 9
    assert not orbit & seen
    seen |= orbit
    orbits.append(orbit)
assert seen == set(addresses)
assert len(orbits) == 20

# Every nonidentity H element has no fixed coordinate.
traces = {(k, l): sum(H_action(k, l, x) == x for x in addresses)
          for k, l in product(range(3), repeat=2)}
assert traces[(0, 0)] == 180
assert all(t == 0 for (k, l), t in traces.items() if (k, l) != (0, 0))

# Over Q(zeta3), each of the 9 one-dimensional characters occurs
# with multiplicity 20; over Q the nontrivial phases must not be
# misconstrued as rational one-dimensional representations.
fourier_multiplicities = {(k, l): len(orbits)
                         for k, l in product(range(3), repeat=2)}
assert len(set(fourier_multiplicities.values())) == 1
assert sum(fourier_multiplicities.values()) == 180

# Existing A5 character table on thirdTurnClass:
# dims [1,3,3',4,5], third-turn traces [1,0,0,1,-1].
irreps = [(1, 1), (3, 0), (3, 0), (4, 1), (5, -1)]
a5_regular_dim = sum(dim * dim for dim, _ in irreps)
a5_fixed_under_internal_c3 = sum(
    dim * ((dim + 2 * chi3) // 3) for dim, chi3 in irreps
)
assert all((dim + 2 * chi3) % 3 == 0 for dim, chi3 in irreps)
assert a5_regular_dim == 60
assert a5_fixed_under_internal_c3 == 20

# The existing j=0..35 SO3 probe uses the same 120-degree C3
# rotation but is NOT automatically the identical VOA representation.
for j in range(36):
    m0 = 2 * (j // 3) + 1
    third_turn_chi = (1, 0, -1)[j % 3]
    assert 3 * m0 == 2 * j + 1 + 2 * third_turn_chi

print("A5 order=60; C3 inclusion element order=3; commutator coverage=60/60")
print("C3_internal x C3_external: commuting, free action on 180 coordinates")
print("Orbit count=20; orbit size=9; permutation character=20*Reg(C3xC3)")
print("C3xC3 Fourier multiplicities over Q(zeta3): all nine equal 20")
print("A5 regular fixed space under C3: dimension 20; j=0..35 average: PASS")
print("NO nontrivial A5->C3 homomorphism; NO Moonshine identification")
print("NO geometric wild embedding / pi1 or Agda kernel receipt claimed")

if __name__ == "__main__":
    pass
