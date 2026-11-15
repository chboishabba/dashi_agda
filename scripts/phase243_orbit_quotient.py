from __future__ import annotations

from collections import Counter
from itertools import product
from typing import Dict, Iterable, List, Tuple

F3 = (0, 1, 2)
CoreState = Tuple[int, int, int, int, int]
Core54Tag = Tuple[int, int, int, int]


def all_core_states() -> List[CoreState]:
    return list(product(F3, repeat=5))


def advance(state: CoreState) -> CoreState:
    k, u, v, p, q = state
    return k, u, v, (p + 1) % 3, (q + 1) % 3


def invert(state: CoreState) -> CoreState:
    k, u, v, p, q = state
    return k, u, v, (-p) % 3, (-q) % 3


def orbit(seed: CoreState) -> frozenset[CoreState]:
    seen = {seed}
    frontier = [seed]
    while frontier:
        state = frontier.pop()
        for action in (advance, invert):
            image = action(state)
            if image not in seen:
                seen.add(image)
                frontier.append(image)
    return frozenset(seen)


def orbit_profile() -> Dict[int, int]:
    unseen = set(all_core_states())
    profile: Counter[int] = Counter()
    while unseen:
        component = orbit(next(iter(unseen)))
        unseen -= set(component)
        profile[len(component)] += 1
    return dict(sorted(profile.items()))


def relative_phase_kind(p: int, q: int) -> int:
    """0 for equal phase, 1 for the unique nonzero relative-phase orbit."""
    return 0 if p == q else 1


def quotient_tag(state: CoreState) -> Core54Tag:
    k, u, v, p, q = state
    return k, u, v, relative_phase_kind(p, q)


def representative(tag: Core54Tag) -> CoreState:
    k, u, v, relative = tag
    if relative not in (0, 1):
        raise ValueError("relative phase kind must be 0 or 1")
    return k, u, v, 0, 0 if relative == 0 else 1


def quotient_representatives() -> List[CoreState]:
    tags = sorted({quotient_tag(state) for state in all_core_states()})
    return [representative(tag) for tag in tags]


def summary() -> dict:
    states = all_core_states()
    tags = {quotient_tag(state) for state in states}
    return {
        "core_state_count": len(states),
        "orbit_profile": orbit_profile(),
        "quotient_class_count": len(tags),
        "compression_factor": len(states) / len(tags),
        "representative_count": len(quotient_representatives()),
    }


if __name__ == "__main__":
    print(summary())
