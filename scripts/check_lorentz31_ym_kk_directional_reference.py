#!/usr/bin/env python3
"""Independent finite reference for the source-written Lorentz31/KK/YM tranche.

Original mathematics: signed quadratic inertia, Hodge star in 4D.
DASHI code: selected finite enumeration and observer/source-owner correspondence.
This script DOES NOT execute Agda or establish a physical 3+1 emergence.
"""
from itertools import product, permutations

AXES = range(4)
SPACE, TIME = "space", "time"
BASIS = ("01", "02", "03", "12", "13", "23")

def count_signature(sign):
    return sum(x == SPACE for x in sign), sum(x == TIME for x in sign)

def oriented_probe_signs(probe):
    return tuple(TIME if x else SPACE for x in probe)

def test_probe():
    good = 0
    rejected = 0
    for arrow in AXES:
        probe = tuple(i == arrow for i in AXES)
        calibrated = oriented_probe_signs(probe)
        assert count_signature(calibrated) == (3, 1)
        for sign in product((SPACE, TIME), repeat=4):
            if sign == calibrated:
                good += 1
            else:
                rejected += 1
            if sign == calibrated:
                assert count_signature(sign) != (1, 3)
    assert (good, rejected) == (4, 60)
    return good, rejected

def hodge(lorentzian, sign, b):
    if b == "01": return sign, "23"
    if b == "02": return -sign, "13"
    if b == "03": return sign, "12"
    if b == "12": return (-sign if lorentzian else sign), "03"
    if b == "13": return (sign if lorentzian else -sign), "02"
    if b == "23": return (-sign if lorentzian else sign), "01"
    raise ValueError(b)

def test_hodge():
    n = 0
    for sign in (1, -1):
        for basis in BASIS:
            e2 = hodge(False, *hodge(False, sign, basis))
            l2 = hodge(True, *hodge(True, sign, basis))
            assert e2 == (sign, basis)
            assert l2 == (-sign, basis)
            n += 1
    assert hodge(True, 1, "23") != hodge(False, 1, "23")
    return n

def orbit_profile(mask, shell):
    points = [v for v in product((-1,0,1), repeat=4)
              if abs(sum(m*x*x for m,x in zip(mask, v))) == shell]
    spatial = [i for i, s in enumerate(mask) if s > 0]
    temporal = [i for i, s in enumerate(mask) if s < 0]
    actions = []
    for perm_s in permutations(spatial):
        for perm_t in permutations(temporal):
            perm = list(range(4))
            for a,b in zip(spatial, perm_s): perm[a] = b
            for a,b in zip(temporal, perm_t): perm[a] = b
            for flips in product((-1,1), repeat=4):
                actions.append((tuple(perm), flips))
    remaining = list(points)
    sizes = []
    fuel = len(points)
    while remaining and fuel > 0:
        head, *tail = remaining
        orbit = {tuple(flips[i]*head[perm[i]] for i in range(4))
                 for perm,flips in actions}
        sizes.append(len(orbit))
        remaining = [x for x in tail if x not in orbit]
        fuel -= 1
    assert not remaining, "fuel stopped before all orbit representatives"
    return sorted(sizes, reverse=True)

def test_profiles():
    plus3_minus1 = (1,1,1,-1)
    plus1_minus3 = (1,-1,-1,-1)
    expected = ([24,6,2], [16,12])
    assert tuple(orbit_profile(plus3_minus1,k) for k in (1,2)) == expected
    assert tuple(orbit_profile(plus1_minus3,k) for k in (1,2)) == expected
    return expected

if __name__ == "__main__":
    selected, rejected = test_probe()
    forms = test_hodge()
    p1, p2 = test_profiles()
    print(f"PASS: 4 calibrated arrows, {rejected} other assignments rejected")
    print(f"PASS: {forms} signed 2-form cases each: Euclidean *^2=+I, Lorentz *^2=-I")
    print(f"PASS: unsigned shells {p1} and {p2} coincide under sign reversal")
    print("LIMIT: no independent continuum physics calibration or Agda kernel run")
