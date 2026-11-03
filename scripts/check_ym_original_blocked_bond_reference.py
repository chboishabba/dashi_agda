#!/usr/bin/env python3
"""Finite exact reference for native four-torus site/bond block coordinates.

Agda owner: BalabanBlockedPeriodicLattice's finePoint/splitFinePoint via
YMClayNativeCyclicFinIsoSafeExact and YMClayNativeBlockedPeriodicBondWeldExact.
The arithmetic convention checked is fine coordinate = coarse * blockSide
+ offset (matching Fin.combine/remQuot). This does NOT compute Wilson
coarse links or establish measure disintegration/continuum convergence.
"""
from itertools import product


def verify(coarse_side, block_side):
    fine_side = coarse_side * block_side
    nsites = fine_side**4
    seen = set()
    for site in product(range(fine_side), repeat=4):
        coarse = tuple(x // block_side for x in site)
        offset = tuple(x % block_side for x in site)
        recovered = tuple(c * block_side + o for c, o in zip(coarse, offset))
        assert recovered == site
        assert all(0 <= c < coarse_side for c in coarse)
        assert all(0 <= o < block_side for o in offset)
        seen.add((coarse, offset))
        for axis in range(4):
            # The axis label does NOT disappear under blocking.
            blocked_bond = (coarse, offset, axis)
            restored_bond = (*recovered, blocked_bond[-1])
            assert restored_bond == (*site, axis)
    assert len(seen) == nsites
    for coarse in product(range(coarse_side), repeat=4):
        for offset in product(range(block_side), repeat=4):
            site = tuple(c*block_side+o for c, o in zip(coarse, offset))
            assert tuple(x//block_side for x in site) == coarse
            assert tuple(x%block_side for x in site) == offset
    return nsites, 4*nsites


if __name__ == "__main__":
    for m,l in ((1, 1), (2, 2), (3, 2), (2, 3), (4, 2)):
        sites,bonds = verify(m,l)
        print(f"coarse={m}, block={l}, fine={m*l}: "
              f"sites={sites}, positive bonds={bonds}; two-way codec PASS")
    print("REFERENCE ONLY: not Agda kernel, gauge-link RG, physical Haar or Clay")
