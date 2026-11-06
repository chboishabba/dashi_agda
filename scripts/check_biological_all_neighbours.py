#!/usr/bin/env python3
"""Independent finite regression for all-incident-bond synchronous tissue updates.

Biological fixture only; not an independently calibrated electrodiffusion law.
"""
from itertools import product
from random import Random

TRITS = (-1, 0, 1)
VOXELS = tuple(product(TRITS, repeat=3))
ACTIONS = ("signal", "wound", "connect", "restoreMemory", "provideEnvironment")


def positive_bonds():
    bonds = []
    for axis in range(3):
        for lo, hi in ((-1, 0), (0, 1)):
            for fixed in product(TRITS, repeat=2):
                source = list(fixed)
                source.insert(axis, lo)
                target = list(fixed)
                target.insert(axis, hi)
                bonds.append((tuple(source), tuple(target)))
    assert len(set(bonds)) == 54
    return tuple(bonds)


BONDS = positive_bonds()
NEIGHBOURS = {v: set() for v in VOXELS}
for a, b in BONDS:
    NEIGHBOURS[a].add(b)
    NEIGHBOURS[b].add(a)


def ordinary_step(action, s):
    g, c, h, j, e, p = s
    if action == "signal":
        p = g and h and j and e
    elif action == "wound":
        p = False
    elif action == "connect":
        j = True
    elif action == "restoreMemory":
        h = True
    elif action == "provideEnvironment":
        e = True
    else:
        raise ValueError(action)
    return (g, c, h, j, e, p)


def project(s):
    g, _c, h, j, e, p = s
    return (g, h, j, e, p)


def fine_update(action, field):
    result = {}
    for v, s in field.items():
        next_state = ordinary_step(action, s)
        if action == "signal":
            g, c, h, j, e, _p = next_state
            new_morphology = g and h and j and e and any(
                field[n][3] for n in NEIGHBOURS[v]
            )
            next_state = (g, c, h, j, e, new_morphology)
        result[v] = next_state
    return result


def coarse_update(action, field):
    result = {}
    for v, (g, h, j, e, p) in field.items():
        if action == "signal":
            p = g and h and j and e and any(
                field[n][2] for n in NEIGHBOURS[v]
            )
        elif action == "wound":
            p = False
        elif action == "connect":
            j = True
        elif action == "restoreMemory":
            h = True
        elif action == "provideEnvironment":
            e = True
        else:
            raise ValueError(action)
        result[v] = (g, h, j, e, p)
    return result


def main():
    degree_histogram = {degree: sum(len(NEIGHBOURS[v]) == degree for v in VOXELS)
                        for degree in (3, 4, 5, 6)}
    assert degree_histogram == {3: 8, 4: 12, 5: 6, 6: 1}
    assert sum(map(len, NEIGHBOURS.values())) == 108
    assert all(a in NEIGHBOURS[b] and b in NEIGHBOURS[a] for a, b in BONDS)
    base = {v: (False, False, False, False, False, False) for v in VOXELS}
    base[(0, 0, 0)] = (True, False, True, True, True, False)
    altered = dict(base)
    altered[(1, 0, 0)] = (False, False, False, True, False, False)
    assert fine_update("signal", base)[(0, 0, 0)][5] is False
    assert fine_update("signal", altered)[(0, 0, 0)][5] is True

    random = Random(20261106)
    for _ in range(32):
        field = {
            v: tuple(bool(random.getrandbits(1)) for _ in range(6))
            for v in VOXELS
        }
        coarse = {v: project(s) for v, s in field.items()}
        for action in ACTIONS * 3:
            field = fine_update(action, field)
            coarse = coarse_update(action, coarse)
            assert {v: project(s) for v, s in field.items()} == coarse
    print("PASS: all 54 undirected bonds used symmetrically, no periodic wrap")
    print("PASS: degree distribution: 8 corners, 12 edge centres, 6 face centres, 1 core")
    print("PASS: one proper neighbour changes a source morphology response")
    print("PASS: 32 x 15-action traces preserve spatial phenotype projection")


if __name__ == "__main__":
    main()
