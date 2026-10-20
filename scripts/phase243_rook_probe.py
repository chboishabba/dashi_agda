from __future__ import annotations

from collections import Counter
from itertools import product
from typing import Dict, List, Tuple

F3 = (0, 1, 2)
AXIS = 3
CoreCode = Tuple[int, int, int, int, int]
BoundaryCode = Tuple[int, int, int]
Plane = Tuple[int, int]
PlanePair = Tuple[Plane, Plane]


def _other_two(missing: int) -> Tuple[int, int]:
    return tuple(x for x in F3 if x != missing)  # type: ignore[return-value]


def decode_core_base(code: Tuple[int, int, int]) -> PlanePair:
    kind, u, v = code
    if kind == 0:
        return ((u, AXIS), (u, v))
    if kind == 1:
        h1, h2 = _other_two(v)
        return ((u, h1), (u, h2))
    if kind == 2:
        c1, c2 = _other_two(u)
        return ((c1, v), (c2, v))
    raise ValueError(code)


def encode_core_base(pair: PlanePair) -> Tuple[int, int, int]:
    (c1, h1), (c2, h2) = pair
    if c1 == c2:
        if AXIS in (h1, h2):
            h = h2 if h1 == AXIS else h1
            return (0, c1, h)
        missing = next(x for x in F3 if x not in (h1, h2))
        return (1, c1, missing)
    if h1 == h2 and h1 != AXIS:
        missing = next(x for x in F3 if x not in (c1, c2))
        return (2, missing, h1)
    raise ValueError(pair)


def decode_boundary_base(missing_channel: int) -> PlanePair:
    c1, c2 = _other_two(missing_channel)
    return ((c1, AXIS), (c2, AXIS))


def encode_boundary_base(pair: PlanePair) -> int:
    c1, c2 = pair[0][0], pair[1][0]
    return next(x for x in F3 if x not in (c1, c2))


def core_base_pairs() -> List[PlanePair]:
    return [decode_core_base(x) for x in product(F3, repeat=3)]


def core_roundtrip_ok() -> bool:
    return all(
        encode_core_base(decode_core_base(x)) == x
        for x in product(F3, repeat=3)
    )


def boundary_roundtrip_ok() -> bool:
    return all(
        encode_boundary_base(decode_boundary_base(x)) == x
        for x in F3
    )


def c3_core(x: CoreCode) -> CoreCode:
    k, u, v, p, q = x
    return k, u, v, (p + 1) % 3, (q + 1) % 3


def invert_core(x: CoreCode) -> CoreCode:
    k, u, v, p, q = x
    return k, u, v, (-p) % 3, (-q) % 3


def c3_boundary(x: BoundaryCode) -> BoundaryCode:
    m, p, q = x
    return m, (p + 1) % 3, (q + 1) % 3


def invert_boundary(x: BoundaryCode) -> BoundaryCode:
    m, p, q = x
    return m, (-p) % 3, (-q) % 3


def _orbit_profile(states, generators) -> Dict[int, int]:
    unseen = set(states)
    sizes = []
    while unseen:
        seed = next(iter(unseen))
        orbit = {seed}
        stack = [seed]
        while stack:
            x = stack.pop()
            for g in generators:
                y = g(x)
                if y not in orbit:
                    orbit.add(y)
                    stack.append(y)
        unseen -= orbit
        sizes.append(len(orbit))
    return dict(sorted(Counter(sizes).items()))


def core_orbit_profile() -> Dict[int, int]:
    states = list(product(F3, repeat=5))
    return _orbit_profile(states, [c3_core, invert_core])


def boundary_orbit_profile() -> Dict[int, int]:
    states = list(product(F3, repeat=3))
    return _orbit_profile(states, [c3_boundary, invert_boundary])


def accounting() -> Dict[str, int]:
    return {
        "phase_pairs": 630,
        "same_plane": 36,
        "rook": 270,
        "nonrook": 324,
        "core": 243,
        "axis_boundary": 27,
    }


def verify() -> Dict[str, object]:
    assert len(set(core_base_pairs())) == 27
    assert core_roundtrip_ok()
    assert boundary_roundtrip_ok()
    assert core_orbit_profile() == {3: 27, 6: 27}
    assert boundary_orbit_profile() == {3: 3, 6: 3}
    a = accounting()
    assert a["same_plane"] + a["rook"] + a["nonrook"] == a["phase_pairs"]
    assert a["core"] + a["axis_boundary"] == a["rook"]
    return {
        "core_base_count": 27,
        "core_orbits": core_orbit_profile(),
        "boundary_orbits": boundary_orbit_profile(),
        "accounting": a,
    }


if __name__ == "__main__":
    print(verify())
