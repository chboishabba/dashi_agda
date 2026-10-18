from __future__ import annotations

from collections import Counter
from itertools import product

TRITS = (-1, 0, 1)
DISTINGUISHED_LANE = ("mode09", 0)
EXCEPTIONAL_LANE = ("mode09", 1)

MODE_TO_INNER_REP = {
    "mode09": (0, 0),
    "mode18": (-1, 0),
    "mode27": (0, -1),
    "mode36": (-1, -1),
    "mode45": (-1, 1),
}


def negate(state: tuple[int, int, int]) -> tuple[int, int, int]:
    x, y, z = state
    return (-x, -y, -z)


def global_orbit(state: tuple[int, int, int]) -> tuple[int, int, int]:
    return min(state, negate(state))


def residual_lanes() -> list[tuple[str, int]]:
    return [
        ("mode09", -1),
        ("mode09", 1),
        ("mode18", -1),
        ("mode18", 0),
        ("mode18", 1),
        ("mode27", -1),
        ("mode27", 0),
        ("mode27", 1),
        ("mode36", -1),
        ("mode36", 0),
        ("mode36", 1),
        ("mode45", -1),
        ("mode45", 0),
        ("mode45", 1),
    ]


def canonical_lift(lane: tuple[str, int]) -> tuple[int, int, int]:
    mode, phase = lane
    y, z = MODE_TO_INNER_REP[mode]
    return (phase, y, z)


def natural_global_target(lane: tuple[str, int]) -> tuple[int, int, int]:
    return global_orbit(canonical_lift(lane))


def explicit_weld_target(lane: tuple[str, int]) -> tuple[int, int, int]:
    if lane == EXCEPTIONAL_LANE:
        return (0, 0, 0)
    return natural_global_target(lane)


def build_probe() -> dict[str, object]:
    raw_states = list(product(TRITS, repeat=3))
    all_global_orbits = {global_orbit(state) for state in raw_states}
    lanes = residual_lanes()
    natural_targets = [natural_global_target(lane) for lane in lanes]
    target_counts = Counter(natural_targets)
    duplicates = [target for target, count in target_counts.items() if count > 1]
    missing = list(all_global_orbits - set(natural_targets))
    weld_targets = [explicit_weld_target(lane) for lane in lanes]
    fixed_orbits = {orbit for orbit in all_global_orbits if orbit == negate(orbit)}

    assert len(duplicates) == 1
    assert len(missing) == 1

    return {
        "raw_state_count": len(raw_states),
        "residual_lane_count": len(lanes),
        "global_inversion_orbit_count": len(all_global_orbits),
        "canonical_lift_image_count": len(set(natural_targets)),
        "canonical_lift_duplicate_orbit": duplicates[0],
        "canonical_lift_missing_orbit": missing[0],
        "explicit_weld_image_count": len(set(weld_targets)),
        "explicit_weld_is_bijection": (
            set(weld_targets) == all_global_orbits
            and len(weld_targets) == len(set(weld_targets))
        ),
        "explicit_weld_is_canonical_lift_induced": all(
            explicit_weld_target(lane) == natural_global_target(lane)
            for lane in lanes
        ),
        "exceptional_lane": EXCEPTIONAL_LANE,
        "exceptional_lane_natural_target": natural_global_target(EXCEPTIONAL_LANE),
        "exceptional_lane_weld_target": explicit_weld_target(EXCEPTIONAL_LANE),
        "global_inversion_invariant_for_all_27_states": all(
            global_orbit(state) == global_orbit(negate(state))
            for state in raw_states
        ),
        "fixed_orbits": fixed_orbits,
        "nonfixed_orbit_count": len(all_global_orbits - fixed_orbits),
        "weld_creates_monster_action": False,
    }


if __name__ == "__main__":
    print(build_probe())
