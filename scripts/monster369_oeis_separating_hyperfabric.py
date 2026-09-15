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
    "balanced196830Bulk": "typedCarrierMap",
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


@dataclass(frozen=True)
class TransversalSearchResult:
    minimum_size: int
    transversals: tuple[tuple[str, ...], ...]


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


def minimum_transversals(
    coordinates: Sequence[str] = COORDINATES,
) -> TransversalSearchResult:
    universe = tuple(coordinates)
    _validate_coordinate_names(universe)
    if len(set(universe)) != len(universe):
        raise ValueError("coordinate universe contains duplicates")

    for size in range(len(universe) + 1):
        hits: list[tuple[str, ...]] = []
        for candidate in itertools.combinations(universe, size):
            if hits_every_edge(candidate):
                hits.append(tuple(sorted(candidate)))
        if hits:
            return TransversalSearchResult(
                minimum_size=size,
                transversals=tuple(sorted(set(hits))),
            )
    raise RuntimeError("finite hypergraph unexpectedly has no transversal")


def incidence_matrix() -> dict[str, dict[str, bool]]:
    return {
        consumer: {coordinate: coordinate in edge for coordinate in COORDINATES}
        for consumer, edge in EDGES.items()
    }


def build_report() -> dict[str, object]:
    search = minimum_transversals()
    return {
        "schema": "monster369-oeis-separating-hyperfabric-runtime-v1",
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
        "authority": {
            "python_runtime_creates_monster_theorem": False,
            "oeis_identity_creates_monster_action": False,
            "coordinate_selection_creates_consumer_proof": False,
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
