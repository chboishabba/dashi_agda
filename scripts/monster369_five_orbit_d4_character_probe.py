from __future__ import annotations

import json


TRITS = (-1, 0, 1)


def quotient_orbit(point: tuple[int, int]) -> str:
    x, y = point
    if x == 0 and y == 0:
        return "zeroOrbit"
    if y == 0:
        return "firstAxisOrbit"
    if x == 0:
        return "secondAxisOrbit"
    if x == y:
        return "equalSignOrbit"
    return "oppositeSignOrbit"


ORBIT_REPRESENTATIVES: dict[str, tuple[int, int]] = {
    "zeroOrbit": (0, 0),
    "firstAxisOrbit": (1, 0),
    "secondAxisOrbit": (0, 1),
    "equalSignOrbit": (1, 1),
    "oppositeSignOrbit": (1, -1),
}


def e(p: tuple[int, int]) -> tuple[int, int]:
    return p


def r90(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (-y, x)


def r180(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (-x, -y)


def r270(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (y, -x)


def reflect_x(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (x, -y)


def reflect_y(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (-x, y)


def reflect_diag(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (y, x)


def reflect_antidiag(p: tuple[int, int]) -> tuple[int, int]:
    x, y = p
    return (-y, -x)


D4_ELEMENTS = {
    "e": e,
    "r2": r180,
    "r": r90,
    "r3": r270,
    "sx": reflect_x,
    "sy": reflect_y,
    "sd": reflect_diag,
    "sad": reflect_antidiag,
}

CONJUGACY_CLASSES = (
    ("identity", ("e",)),
    ("half_turn", ("r2",)),
    ("quarter_turns", ("r", "r3")),
    ("axis_reflections", ("sx", "sy")),
    ("diagonal_reflections", ("sd", "sad")),
)

IRREP_CHARACTERS = {
    "A1": [1, 1, 1, 1, 1],
    "A2": [1, 1, 1, -1, -1],
    "B1": [1, 1, -1, 1, -1],
    "B2": [1, 1, -1, -1, 1],
    "E": [2, -2, 0, 0, 0],
}
IRREP_DIMENSIONS = {"A1": 1, "A2": 1, "B1": 1, "B2": 1, "E": 2}


def orbit_action(element: str, orbit: str) -> str:
    transform = D4_ELEMENTS[element]
    return quotient_orbit(transform(ORBIT_REPRESENTATIVES[orbit]))


def fixed_orbit_count(element: str) -> int:
    return sum(
        orbit_action(element, orbit) == orbit
        for orbit in ORBIT_REPRESENTATIVES
    )


def class_character() -> list[int]:
    values: list[int] = []
    for _, members in CONJUGACY_CLASSES:
        member_values = {fixed_orbit_count(member) for member in members}
        assert len(member_values) == 1
        values.append(next(iter(member_values)))
    return values


def weighted_inner_product_split(left: list[int], right: list[int]) -> dict[str, int]:
    class_sizes = [len(members) for _, members in CONJUGACY_CLASSES]
    terms = [
        size * a * b for size, a, b in zip(class_sizes, left, right, strict=True)
    ]
    positive = sum(term for term in terms if term > 0)
    negative = sum(-term for term in terms if term < 0)
    numerator = positive - negative
    assert numerator % 8 == 0
    return {
        "positive": positive,
        "negative": negative,
        "multiplicity": numerator // 8,
    }


def character_inner_product(left: list[int], right: list[int]) -> int:
    return weighted_inner_product_split(left, right)["multiplicity"]


def decompose(character: list[int]) -> dict[str, int]:
    return {
        irrep: character_inner_product(character, irrep_character)
        for irrep, irrep_character in IRREP_CHARACTERS.items()
    }


def build_report() -> dict[str, object]:
    character = class_character()
    multiplicities = decompose(character)
    weighted_splits = {
        irrep: weighted_inner_product_split(character, irrep_character)
        for irrep, irrep_character in IRREP_CHARACTERS.items()
    }
    dimension_check = sum(
        multiplicities[name] * IRREP_DIMENSIONS[name]
        for name in multiplicities
    )

    raw_nine = {"A1": 3, "A2": 0, "B1": 1, "B2": 1, "E": 2}
    removed = {
        name: raw_nine[name] - multiplicities[name]
        for name in raw_nine
        if raw_nine[name] != multiplicities[name]
    }
    removed_dimension = sum(removed[name] * IRREP_DIMENSIONS[name] for name in removed)

    return {
        "schema": "monster369-five-orbit-d4-character-probe-v2",
        "orbit_count": len(ORBIT_REPRESENTATIVES),
        "orbits": list(ORBIT_REPRESENTATIVES),
        "conjugacy_classes": [name for name, _ in CONJUGACY_CLASSES],
        "conjugacy_class_sizes": [len(members) for _, members in CONJUGACY_CLASSES],
        "permutation_character": character,
        "irrep_multiplicities": multiplicities,
        "weighted_inner_product_splits": weighted_splits,
        "quotient_irrep_multiplicities": multiplicities,
        "raw_nine_irrep_multiplicities": raw_nine,
        "dimension_check": dimension_check,
        "removed_irrep_content": removed,
        "removed_dimension": removed_dimension,
        "one_to_one_orbit_to_irrep_semantic_map_paid": False,
        "quotient_character_decomposition_paid_by_python": True,
        "agda_kernel_character_decomposition_paid": False,
        "monster_42d_action_paid": False,
    }


def main() -> int:
    print(json.dumps(build_report(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
