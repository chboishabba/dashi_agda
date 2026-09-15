from __future__ import annotations

import argparse
import itertools
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


COORDINATES: tuple[str, ...] = (
    "ternary3Arithmetic",
    "zetaTrit6Carrier",
    "nonary9Carrier",
    "hypervoxel27Carrier",
    "zeta54Carrier",
    "multiplicity90Arithmetic",
    "heisenberg729Carrier",
    "monster3B65610Character",
    "balanced196830Bulk",
    "monster196883Degree",
    "moonshine196884Dimension",
    "ogg475971Factor",
    "zetaPhaseCoordinate",
    "tauModularCoordinate",
    "actualWeylActionCoordinate",
    "selected3BRestrictionCoordinate",
    "twelvePlusSeventyEightCoordinate",
    "oeisA000244Coordinate",
    "oeisA005052Coordinate",
    "oeisA001379Coordinate",
    "oeisA309510Coordinate",
    "oeisA199014Coordinate",
    "sameIntegerCollisionOnly",
)

RELATION_STRENGTH: dict[str, str] = {
    "ternary3Arithmetic": "exactArithmetic",
    "zetaTrit6Carrier": "typedCarrierMap",
    "nonary9Carrier": "typedCarrierMap",
    "hypervoxel27Carrier": "typedCarrierMap",
    "zeta54Carrier": "typedCarrierMap",
    "multiplicity90Arithmetic": "exactArithmetic",
    "heisenberg729Carrier": "typedCarrierMap",
    "monster3B65610Character": "representationActionTheorem",
    "balanced196830Bulk": "representationActionTheorem",
    "monster196883Degree": "representationActionTheorem",
    "moonshine196884Dimension": "representationActionTheorem",
    "ogg475971Factor": "exactArithmetic",
    "zetaPhaseCoordinate": "typedCarrierMap",
    "tauModularCoordinate": "typedCarrierMap",
    "actualWeylActionCoordinate": "representationActionTheorem",
    "selected3BRestrictionCoordinate": "representationActionTheorem",
    "twelvePlusSeventyEightCoordinate": "representationActionTheorem",
    "oeisA000244Coordinate": "oeisNavigation",
    "oeisA005052Coordinate": "oeisNavigation",
    "oeisA001379Coordinate": "oeisNavigation",
    "oeisA309510Coordinate": "oeisNavigation",
    "oeisA199014Coordinate": "oeisNavigation",
    "sameIntegerCollisionOnly": "unpaidCoincidence",
}

EDGES: dict[str, frozenset[str]] = {
    "phaseResolutionConsumer": frozenset(
        {"zetaPhaseCoordinate", "monster3B65610Character", "zeta54Carrier"}
    ),
    "inversionConsumer": frozenset(
        {"zetaPhaseCoordinate", "tauModularCoordinate", "actualWeylActionCoordinate"}
    ),
    "heisenbergRecognitionConsumer": frozenset(
        {"heisenberg729Carrier", "zeta54Carrier", "actualWeylActionCoordinate"}
    ),
    "threeBRestrictionConsumer": frozenset(
        {
            "selected3BRestrictionCoordinate",
            "monster3B65610Character",
            "monster196883Degree",
        }
    ),
    "multiplicityTwelveSeventyEightConsumer": frozenset(
        {
            "twelvePlusSeventyEightCoordinate",
            "selected3BRestrictionCoordinate",
            "actualWeylActionCoordinate",
        }
    ),
}

CANONICAL_TYPED_SELECTION = frozenset(
    {
        "zetaPhaseCoordinate",
        "actualWeylActionCoordinate",
        "selected3BRestrictionCoordinate",
        "twelvePlusSeventyEightCoordinate",
    }
)

OEIS_ONLY_SELECTION = frozenset(
    {
        "oeisA000244Coordinate",
        "oeisA005052Coordinate",
        "oeisA001379Coordinate",
        "oeisA309510Coordinate",
        "oeisA199014Coordinate",
    }
)

PROOF_ELIGIBLE_COORDINATES: tuple[str, ...] = tuple(
    coordinate
    for coordinate in COORDINATES
    if RELATION_STRENGTH[coordinate]
    in {"typedCarrierMap", "representationActionTheorem"}
)


@dataclass(frozen=True)
class TransversalSearchResult:
    minimum_size: int
    transversals: tuple[tuple[str, ...], ...]


@dataclass(frozen=True)
class LiteralWorld:
    name: str
    observed_integer: int
    role: str
    observations: dict[str, str]


@dataclass(frozen=True)
class LiteralCollisionEdge:
    common_integer: int
    left_world: str
    right_world: str
    coordinates: frozenset[str]


LITERAL_WORLDS: tuple[LiteralWorld, ...] = (
    LiteralWorld(
        "oeis42dCoefficient17496",
        17496,
        "OEIS A058678 / Monster class-42d McKay-Thompson coefficient",
        {"sameIntegerCollisionOnly": "A058678-42d-coefficient"},
    ),
    LiteralWorld(
        "n3bRestrictionDegree17496",
        17496,
        "source-paid N(3B) restriction degree 2*729*12",
        {
            "selected3BRestrictionCoordinate": "N3B-restriction-17496",
            "twelvePlusSeventyEightCoordinate": "12-block-occurrence",
            "sameIntegerCollisionOnly": "N3B-restriction-role",
        },
    ),
    LiteralWorld(
        "oeisA005052Level8_65610",
        65610,
        "OEIS A005052 level 8 numerical-family coordinate",
        {
            "oeisA005052Coordinate": "A005052-level8",
            "sameIntegerCollisionOnly": "A005052-numerical-role",
        },
    ),
    LiteralWorld(
        "monster3BRegularMultiplicity65610",
        65610,
        "Monster 3B regular C3 character multiplicity",
        {
            "monster3B65610Character": "3B-regular-character-multiplicity",
            "selected3BRestrictionCoordinate": "3B-restriction-character-role",
            "sameIntegerCollisionOnly": "3B-character-role",
        },
    ),
    LiteralWorld(
        "base369BulkPlus53_196883",
        196883,
        "Base369 10*3^9 bulk plus residual 53",
        {
            "balanced196830Bulk": "196830-plus-53",
            "sameIntegerCollisionOnly": "Base369-bulk-residual-role",
        },
    ),
    LiteralWorld(
        "oggTripleFactor196883",
        196883,
        "47*59*71 arithmetic/Ogg-prime factor presentation",
        {
            "ogg475971Factor": "47*59*71",
            "sameIntegerCollisionOnly": "factorisation-role",
        },
    ),
    LiteralWorld(
        "monsterIrreducibleDegree196883",
        196883,
        "Monster irreducible representation degree / OEIS A001379 navigation",
        {
            "monster196883Degree": "Monster-irrep-degree",
            "oeisA001379Coordinate": "A001379-degree-navigation",
            "sameIntegerCollisionOnly": "Monster-degree-role",
        },
    ),
    LiteralWorld(
        "base369BulkPlus54_196884",
        196884,
        "Base369 10*3^9 bulk plus full residual 54",
        {
            "balanced196830Bulk": "196830-plus-54",
            "zeta54Carrier": "typed-54-residual-carrier",
            "sameIntegerCollisionOnly": "Base369-full-residual-role",
        },
    ),
    LiteralWorld(
        "moonshineConformalDimension196884",
        196884,
        "Moonshine/Monster weight-two conformal dimension",
        {
            "moonshine196884Dimension": "Moonshine-weight-two-dimension",
            "sameIntegerCollisionOnly": "Moonshine-dimension-role",
        },
    ),
    LiteralWorld(
        "oeisDivisorSurface196884",
        196884,
        "OEIS A199014 divisor-lattice coordinate",
        {
            "oeisA199014Coordinate": "A199014-divisor-surface",
            "sameIntegerCollisionOnly": "divisor-lattice-role",
        },
    ),
    LiteralWorld(
        "jCoefficient196884",
        196884,
        "classical J / moonshine q coefficient role",
        {
            "tauModularCoordinate": "J-q1-modular-coordinate",
            "sameIntegerCollisionOnly": "J-coefficient-role",
        },
    ),
)


def extract_agda_coordinates(path: Path) -> tuple[str, ...]:
    text = path.read_text(encoding="utf-8")
    header = "data Monster369Coordinate : Set where"
    start = text.index(header) + len(header)
    section_marker = "\n------------------------------------------------------------------------\n-- 2."
    end = text.index(section_marker, start)
    coordinates: list[str] = []
    for line in text[start:end].splitlines():
        stripped = line.strip()
        suffix = " : Monster369Coordinate"
        if stripped.endswith(suffix):
            coordinates.append(stripped[: -len(suffix)])
    if not coordinates:
        raise ValueError(f"no Monster369Coordinate constructors found in {path}")
    return tuple(coordinates)


def _validate_coordinate_names(names: Iterable[str]) -> frozenset[str]:
    selected = frozenset(names)
    unknown = selected.difference(COORDINATES)
    if unknown:
        raise ValueError(f"unknown Monster369 coordinates: {sorted(unknown)}")
    return selected


def hits_edge(selected: Iterable[str], edge: Iterable[str]) -> bool:
    selected_set = _validate_coordinate_names(selected)
    edge_set = frozenset(edge)
    unknown = edge_set.difference(COORDINATES)
    if unknown:
        raise ValueError(f"edge contains unknown coordinates: {sorted(unknown)}")
    return bool(selected_set.intersection(edge_set))


def hits_every_edge(selected: Iterable[str]) -> bool:
    selected_set = _validate_coordinate_names(selected)
    return all(bool(selected_set.intersection(edge)) for edge in EDGES.values())


def _minimum_transversals_for_edges(
    edges: Sequence[frozenset[str]],
    coordinates: Sequence[str],
) -> TransversalSearchResult:
    universe = tuple(coordinates)
    _validate_coordinate_names(universe)
    if len(set(universe)) != len(universe):
        raise ValueError("coordinate universe contains duplicates")

    for size in range(len(universe) + 1):
        hits: list[tuple[str, ...]] = []
        for candidate in itertools.combinations(universe, size):
            selected = set(candidate)
            if all(bool(selected.intersection(edge)) for edge in edges):
                hits.append(tuple(sorted(candidate)))
        if hits:
            return TransversalSearchResult(
                minimum_size=size,
                transversals=tuple(sorted(set(hits))),
            )
    raise RuntimeError("finite hypergraph unexpectedly has no transversal")


def minimum_transversals(
    coordinates: Sequence[str] = COORDINATES,
) -> TransversalSearchResult:
    return _minimum_transversals_for_edges(tuple(EDGES.values()), coordinates)


def literal_collision_edges(
    worlds: Sequence[LiteralWorld] = LITERAL_WORLDS,
) -> tuple[LiteralCollisionEdge, ...]:
    edges: list[LiteralCollisionEdge] = []
    for index, left in enumerate(worlds):
        for right in worlds[index + 1 :]:
            if left.observed_integer != right.observed_integer:
                continue
            coordinates = frozenset(
                coordinate
                for coordinate in COORDINATES
                if left.observations.get(coordinate)
                != right.observations.get(coordinate)
            )
            edges.append(
                LiteralCollisionEdge(
                    common_integer=left.observed_integer,
                    left_world=left.name,
                    right_world=right.name,
                    coordinates=coordinates,
                )
            )
    return tuple(edges)


def literal_edges_hit_by(selected: Iterable[str]) -> bool:
    selected_set = _validate_coordinate_names(selected)
    return all(
        bool(selected_set.intersection(edge.coordinates))
        for edge in literal_collision_edges()
    )


def minimum_literal_collision_transversals() -> TransversalSearchResult:
    proof_edges = tuple(
        frozenset(edge.coordinates.intersection(PROOF_ELIGIBLE_COORDINATES))
        for edge in literal_collision_edges()
    )
    if any(not edge for edge in proof_edges):
        raise RuntimeError(
            "literal collision portfolio contains a pair with no proof-eligible separating coordinate"
        )
    return _minimum_transversals_for_edges(
        proof_edges,
        PROOF_ELIGIBLE_COORDINATES,
    )


def incidence_matrix() -> dict[str, dict[str, bool]]:
    return {
        consumer: {coordinate: coordinate in edge for coordinate in COORDINATES}
        for consumer, edge in EDGES.items()
    }


def literal_incidence_matrix() -> dict[str, dict[str, bool]]:
    matrix: dict[str, dict[str, bool]] = {}
    for edge in literal_collision_edges():
        edge_name = f"{edge.common_integer}:{edge.left_world}!={edge.right_world}"
        matrix[edge_name] = {
            coordinate: coordinate in edge.coordinates for coordinate in COORDINATES
        }
    return matrix


def build_report() -> dict[str, object]:
    search = minimum_transversals()
    literal_search = minimum_literal_collision_transversals()
    literal_edges = literal_collision_edges()
    return {
        "schema": "monster369-oeis-separating-hyperfabric-runtime-v2",
        "portfolio": {
            "coordinate_count": len(COORDINATES),
            "edge_count": len(EDGES),
            "coordinates": list(COORDINATES),
            "relation_strength": RELATION_STRENGTH,
            "edges": {name: sorted(edge) for name, edge in EDGES.items()},
            "incidence_matrix": incidence_matrix(),
        },
        "known_selections": {
            "canonical_typed_selection": sorted(CANONICAL_TYPED_SELECTION),
            "canonical_typed_hits_every_edge": hits_every_edge(CANONICAL_TYPED_SELECTION),
            "oeis_only_selection": sorted(OEIS_ONLY_SELECTION),
        },
        "negative_controls": {
            "oeis_only_hits_every_edge": hits_every_edge(OEIS_ONLY_SELECTION),
            "oeis_only_hits_every_literal_collision_edge": literal_edges_hit_by(
                OEIS_ONLY_SELECTION
            ),
            "same_integer_collision_coordinate_is_unpaid":
                RELATION_STRENGTH["sameIntegerCollisionOnly"] == "unpaidCoincidence",
        },
        "minimum_transversal_search": {
            "minimum_size": search.minimum_size,
            "minimum_transversals": [list(item) for item in search.transversals],
            "search_scope": "current finite declared Monster369 consumer portfolio only",
            "exhaustive_runtime_search_completed": True,
            "kernel_proved_minimum": False,
        },
        "literal_collision_portfolio": {
            "world_count": len(LITERAL_WORLDS),
            "collision_edge_count": len(literal_edges),
            "observed_integers": sorted({world.observed_integer for world in LITERAL_WORLDS}),
            "worlds": [
                {
                    "name": world.name,
                    "observed_integer": world.observed_integer,
                    "role": world.role,
                    "observations": world.observations,
                }
                for world in LITERAL_WORLDS
            ],
            "edges": [
                {
                    "common_integer": edge.common_integer,
                    "left_world": edge.left_world,
                    "right_world": edge.right_world,
                    "coordinates": sorted(edge.coordinates),
                }
                for edge in literal_edges
            ],
            "incidence_matrix": literal_incidence_matrix(),
            "proof_eligible_coordinates": list(PROOF_ELIGIBLE_COORDINATES),
            "runtime_minimum_size": literal_search.minimum_size,
            "runtime_minimum_transversals": [
                list(item) for item in literal_search.transversals
            ],
            "exhaustive_runtime_search_completed": True,
            "kernel_proved_minimum": False,
            "globally_minimal_across_future_worlds": False,
        },
        "authority": {
            "python_runtime_creates_monster_theorem": False,
            "oeis_identity_creates_monster_action": False,
            "coordinate_selection_creates_consumer_proof": False,
            "same_integer_role_collision_creates_same_object": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Exhaustively search the finite Monster369/OEIS separating hypergraph."
    )
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    rendered = json.dumps(build_report(), indent=2, sort_keys=True) + "\n"
    if args.output is None:
        print(rendered, end="")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
