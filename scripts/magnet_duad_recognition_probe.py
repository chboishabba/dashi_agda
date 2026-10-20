from __future__ import annotations

from collections import Counter
from itertools import combinations
from typing import Callable, Dict, Iterable, List, Sequence, Set, Tuple

Point = int
Duad = Tuple[Point, Point]
PhasePoint = Tuple[int, int]
PhasePair = Tuple[PhasePoint, PhasePoint]


def duads() -> List[Duad]:
    """The unordered two-subsets of a 24-point carrier."""
    return list(combinations(range(24), 2))


def rank3_orbit_sizes(seed: Duad = (0, 1)) -> Tuple[int, int, int]:
    """Fixed-duad relation classes: same / intersect in one point / disjoint."""
    counts = Counter(len(set(seed).intersection(d)) for d in duads())
    return counts[2], counts[1], counts[0]


def raw_axis_support_closed_under_c3() -> bool:
    """Whether the 24 real cos/sin axes are permuted by a nontrivial C3 phase.

    They are not: a 120-degree rotation of one harmonic plane maps e_cos to
    (-1/2)e_cos + (sqrt(3)/2)e_sin.  The physical C3 phase therefore acts
    linearly inside a 2-D harmonic plane rather than as a permutation of the
    selected real coordinate axes.
    """
    return False


def _canon_pair(a: PhasePoint, b: PhasePoint) -> PhasePair:
    return tuple(sorted((a, b)))  # type: ignore[return-value]


def _act_pair(pair: PhasePair, action: Callable[[PhasePoint], PhasePoint]) -> PhasePair:
    return _canon_pair(action(pair[0]), action(pair[1]))


def _orbits(
    pairs: Sequence[PhasePair],
    generators: Sequence[Callable[[PhasePoint], PhasePoint]],
) -> List[Set[PhasePair]]:
    unseen: Set[PhasePair] = set(pairs)
    result: List[Set[PhasePair]] = []
    while unseen:
        seed = next(iter(unseen))
        orbit = {seed}
        frontier = [seed]
        while frontier:
            current = frontier.pop()
            for generator in generators:
                image = _act_pair(current, generator)
                if image not in orbit:
                    orbit.add(image)
                    frontier.append(image)
        unseen -= orbit
        result.append(orbit)
    return result


def phase_line_pair_orbit_profile() -> Dict[str, Dict[int, int]]:
    """Orbit profile on the correct phase-resolved projective-line carrier.

    The 24 real axes are grouped into 12 harmonic planes.  Replacing each plane
    by its three C3-related projective phase lines gives 36 phase-line points and
    C(36,2)=630 unordered pairs.  Global phase translation is C3; inversion
    p -> -p supplies the C2 completion.
    """
    points: List[PhasePoint] = [(block, phase) for block in range(12) for phase in range(3)]
    pairs: List[PhasePair] = list(combinations(points, 2))

    def c3(point: PhasePoint) -> PhasePoint:
        block, phase = point
        return block, (phase + 1) % 3

    def c2(point: PhasePoint) -> PhasePoint:
        block, phase = point
        return block, (-phase) % 3

    c3_profile = Counter(map(len, _orbits(pairs, [c3])))
    completed_profile = Counter(map(len, _orbits(pairs, [c3, c2])))
    return {
        "C3": dict(sorted(c3_profile.items())),
        "C3xC2": dict(sorted(completed_profile.items())),
    }


def recognition_summary() -> dict:
    return {
        "raw_coordinate_count": 24,
        "raw_duad_count": len(duads()),
        "fixed_duad_rank3_partition": rank3_orbit_sizes(),
        "raw_axis_support_closed_under_c3": raw_axis_support_closed_under_c3(),
        "phase_harmonic_plane_count": 12,
        "phase_line_count": 36,
        "phase_line_pair_count": 630,
        "phase_line_pair_orbits": phase_line_pair_orbit_profile(),
        "candidate_243_27_6_promoted": False,
    }


if __name__ == "__main__":
    print(recognition_summary())
