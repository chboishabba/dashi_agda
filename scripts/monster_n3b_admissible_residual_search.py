from __future__ import annotations

from collections import defaultdict
from typing import Any

CONSUMER = "which admissible D8 realization/fusion supplies the five-orbit action?"

RESIDUAL_COORDINATES = (
    "d8_conjugacy_class",
    "monster_class_fusion",
    "power_42b14_to_3b",
    "power_42b7_to_6b",
    "five_orbit_character",
    "action_intertwiner_paid",
)

COST_AXES = (
    "ram",
    "matrix_dimension",
    "group_enumeration",
    "candidate_count",
    "proof_debt",
)


def _largest_collision(worlds: list[dict[str, Any]], coordinates: list[str]) -> int:
    buckets: dict[tuple[Any, ...], int] = defaultdict(int)
    for world in worlds:
        key = tuple(_freeze(world.get(coord)) for coord in coordinates)
        buckets[key] += 1
    return max(buckets.values(), default=0)


def _freeze(value: Any) -> Any:
    if isinstance(value, list):
        return tuple(value)
    if isinstance(value, dict):
        return tuple(sorted((k, _freeze(v)) for k, v in value.items()))
    return value


def analyze_worlds(worlds: list[dict[str, Any]]) -> dict[str, Any]:
    if not worlds:
        raise ValueError("at least one residual world is required")
    if not all(world.get("character_compatible") is True for world in worlds):
        raise ValueError("residual search accepts only character-compatible worlds")

    character_collision_size = _largest_collision(worlds, ["character_observer"])
    opened: list[str] = []
    largest = character_collision_size
    next_coordinate: str | None = None

    for coordinate in RESIDUAL_COORDINATES:
        values = [world.get(coordinate) for world in worlds]
        if all(value is None for value in values):
            next_coordinate = coordinate
            if opened:
                opened.append(coordinate)
            else:
                opened = [coordinate]
            break

        opened.append(coordinate)
        largest = _largest_collision(worlds, opened)
        if largest <= 1:
            next_coordinate = None
            break

    return {
        "consumer": CONSUMER,
        "candidate_count": len(worlds),
        "character_collision_size": character_collision_size,
        "character_table_observer_sufficient": character_collision_size <= 1,
        "opened_coordinates": opened,
        "next_coordinate": next_coordinate,
        "largest_remaining_collision": largest,
        "matrix_payload_loaded": False,
        "quotient_route_creates_selected_action": False,
        "runtime_search_creates_factors_through_theorem": False,
    }


def route_costs() -> dict[str, dict[str, int]]:
    # Ordinal engineering costs for this declared consumer only. They are not
    # benchmarks and not universal performance claims.
    return {
        "quotient-permutation": {
            "ram": 1,
            "matrix_dimension": 0,
            "group_enumeration": 1,
            "candidate_count": 17,
            "proof_debt": 2,
        },
        "matrix-78": {
            "ram": 5,
            "matrix_dimension": 78,
            "group_enumeration": 5,
            "candidate_count": 17,
            "proof_debt": 5,
        },
    }


def weakly_dominates(left: dict[str, int], right: dict[str, int]) -> bool:
    return all(left[axis] <= right[axis] for axis in COST_AXES)
