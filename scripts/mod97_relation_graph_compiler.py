#!/usr/bin/env python3
"""Compile paid circuit relation receipts into the canonical beta graph surface.

This adapter is intentionally fail-closed. It consumes only already-paid relation
classifications. A gluingRequirement also needs an explicitly paid direction,
because the current symmetric Mod97 pair-ablation observation cannot identify
which selection-closure direction holds. Independent pairs are retained as audit
metadata but create no graph constraint.

The compiler reuses the exact finite closed-compatible-capacity producer; it does
not create a new relation ontology or promote beta into a Grokking mechanism.
"""

from __future__ import annotations

from typing import Any, Iterable

try:
    from scripts.mod97_closed_compatible_capacity import (
        certify_closed_compatible_capacity,
    )
except ModuleNotFoundError:
    from mod97_closed_compatible_capacity import certify_closed_compatible_capacity

_ALLOWED_RELATIONS = {"conflict", "gluingRequirement", "independent"}
_ALLOWED_DIRECTIONS = {
    "left_requires_right",
    "right_requires_left",
    "mutual_requirement",
}


def _validate_endpoint(node_count: int, value: Any, name: str) -> int:
    if not isinstance(value, int):
        raise ValueError(f"{name} endpoint must be an integer")
    if not 0 <= value < node_count:
        raise ValueError(f"{name} endpoint lies outside candidate carrier")
    return value


def compile_relation_graph(
    *, node_count: int, relation_records: Iterable[dict[str, Any]]
) -> dict[str, Any]:
    if node_count < 0:
        raise ValueError("node_count must be non-negative")

    conflicts: set[tuple[int, int]] = set()
    requirements: set[tuple[int, int]] = set()
    independent: set[tuple[int, int]] = set()
    normalized_records: list[dict[str, Any]] = []

    for record in relation_records:
        if record.get("classification_paid") is not True:
            raise ValueError("relation classification must be paid before graph compilation")

        left = _validate_endpoint(node_count, record.get("left"), "left")
        right = _validate_endpoint(node_count, record.get("right"), "right")
        if left == right:
            raise ValueError("relation endpoints must be distinct")

        relation = record.get("relation")
        if relation not in _ALLOWED_RELATIONS:
            raise ValueError(f"unsupported canonical relation: {relation!r}")

        normalized = {
            "left": left,
            "right": right,
            "relation": relation,
            "classification_paid": True,
        }

        if relation == "conflict":
            conflicts.add((min(left, right), max(left, right)))

        elif relation == "independent":
            independent.add((min(left, right), max(left, right)))

        else:
            if record.get("direction_paid") is not True:
                raise ValueError(
                    "gluingRequirement direction must be paid before graph compilation"
                )
            direction = record.get("direction")
            if direction not in _ALLOWED_DIRECTIONS:
                raise ValueError("gluingRequirement direction is missing or invalid")
            normalized["direction_paid"] = True
            normalized["direction"] = direction

            if direction == "left_requires_right":
                requirements.add((left, right))
            elif direction == "right_requires_left":
                requirements.add((right, left))
            else:
                requirements.add((left, right))
                requirements.add((right, left))

        normalized_records.append(normalized)

    normalized_records.sort(
        key=lambda row: (
            row["left"],
            row["right"],
            row["relation"],
            row.get("direction", ""),
        )
    )

    return {
        "node_count": node_count,
        "canonical_relation_carrier": [
            "conflict",
            "gluingRequirement",
            "independent",
        ],
        "relation_records": normalized_records,
        "conflicts": [list(edge) for edge in sorted(conflicts)],
        "requirements": [list(edge) for edge in sorted(requirements)],
        "independent_pairs": [list(edge) for edge in sorted(independent)],
        "all_relation_classifications_paid": True,
        "all_requirement_directions_paid": True,
        "boundary": (
            "Compilation preserves canonical relation meaning. Conflict is an undirected "
            "coexistence prohibition, gluingRequirement is directed selection closure, "
            "and independent creates no constraint. The compiler cannot manufacture "
            "classification or direction from raw intervention effects."
        ),
    }


def compile_and_certify(
    *, node_count: int, relation_records: Iterable[dict[str, Any]]
) -> dict[str, Any]:
    graph = compile_relation_graph(
        node_count=node_count,
        relation_records=relation_records,
    )
    beta = certify_closed_compatible_capacity(
        node_count=node_count,
        conflicts={tuple(edge) for edge in graph["conflicts"]},
        requirements={tuple(edge) for edge in graph["requirements"]},
    )

    return {
        "producer": "scripts/mod97_relation_graph_compiler.py",
        "compiled_graph": graph,
        "beta_certificate": beta,
        "input_payment": {
            "relation_graph_paid": graph["all_relation_classifications_paid"],
            "requirement_direction_paid": graph["all_requirement_directions_paid"],
        },
        "promotion": {
            "beta_for_supplied_paid_graph": (
                graph["all_relation_classifications_paid"]
                and graph["all_requirement_directions_paid"]
                and beta["maximality_paid_by_finite_exhaustion"]
            ),
            "grokking_mechanism_paid": False,
        },
        "non_promotion_boundary": (
            "A paid supplied relation graph plus exhaustive finite search pays beta only "
            "for that graph. It does not establish that beta changed through Grokking, "
            "that the graph transfers across checkpoints/tasks, or that beta is causal."
        ),
    }
