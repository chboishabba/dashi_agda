#!/usr/bin/env python3
"""Exact finite closed-compatible-capacity certificates for Grokking circuits.

This is the runtime counterpart of the finite beta witness already formalised in
DASHI. A family is usable only when it is both conflict-free and closed under
all directed requirement edges. The implementation exhaustively enumerates the
finite candidate carrier, so its maximality claim is local and exact rather
than heuristic.

The certificate consumes already-classified relations. It does not itself pay
relation classification, empirical Grokking identity, or a mechanism theorem.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

Edge = tuple[int, int]


def _canonical_conflict(edge: Edge) -> Edge:
    left, right = edge
    if left == right:
        raise ValueError("conflict edges must join distinct candidates")
    return (left, right) if left < right else (right, left)


def _validate_nodes(node_count: int, edges: Iterable[Edge]) -> None:
    if node_count < 0:
        raise ValueError("node_count must be non-negative")
    for left, right in edges:
        if not (0 <= left < node_count and 0 <= right < node_count):
            raise ValueError("edge endpoint lies outside candidate carrier")


def is_closed_compatible(
    family: set[int],
    *,
    conflicts: set[Edge],
    requirements: set[Edge],
) -> bool:
    canonical_conflicts = {_canonical_conflict(edge) for edge in conflicts}
    for left, right in canonical_conflicts:
        if left in family and right in family:
            return False

    for requiring, required in requirements:
        if requiring in family and required not in family:
            return False

    return True


def certify_closed_compatible_capacity(
    *,
    node_count: int,
    conflicts: set[Edge],
    requirements: set[Edge],
) -> dict:
    _validate_nodes(node_count, conflicts)
    _validate_nodes(node_count, requirements)
    canonical_conflicts = {_canonical_conflict(edge) for edge in conflicts}

    admissible: list[list[int]] = []
    best_size = -1
    best: list[list[int]] = []

    for mask in range(1 << node_count):
        family = {node for node in range(node_count) if mask & (1 << node)}
        if not is_closed_compatible(
            family,
            conflicts=canonical_conflicts,
            requirements=requirements,
        ):
            continue

        ordered = sorted(family)
        admissible.append(ordered)
        size = len(ordered)
        if size > best_size:
            best_size = size
            best = [ordered]
        elif size == best_size:
            best.append(ordered)

    best.sort()
    admissible.sort(key=lambda family: (len(family), family))

    return {
        "producer": "scripts/mod97_closed_compatible_capacity.py",
        "raw_candidate_count": node_count,
        "conflict_edges": [list(edge) for edge in sorted(canonical_conflicts)],
        "requirement_edges": [list(edge) for edge in sorted(requirements)],
        "beta": max(best_size, 0),
        "maximal_families": best,
        "admissible_family_count": len(admissible),
        "subsets_examined": 1 << node_count,
        "maximality_paid_by_finite_exhaustion": True,
        "relation_classification_paid": False,
        "grokking_mechanism_paid": False,
        "non_promotion_boundary": (
            "Finite exhaustive maximality pays only beta for the supplied relation graph. "
            "It does not establish that those relations were empirically classified, "
            "that beta changed during Grokking, or that beta is a Grokking mechanism."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--node-count", type=int, required=True)
    parser.add_argument(
        "--conflict",
        action="append",
        default=[],
        metavar="I,J",
        help="undirected conflict edge; repeatable",
    )
    parser.add_argument(
        "--requirement",
        action="append",
        default=[],
        metavar="I,J",
        help="directed requirement I->J; repeatable",
    )
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()

    def parse_edge(text: str) -> Edge:
        parts = text.split(",")
        if len(parts) != 2:
            raise ValueError(f"expected I,J edge, got {text!r}")
        return int(parts[0]), int(parts[1])

    receipt = certify_closed_compatible_capacity(
        node_count=args.node_count,
        conflicts={parse_edge(edge) for edge in args.conflict},
        requirements={parse_edge(edge) for edge in args.requirement},
    )
    text = json.dumps(receipt, indent=2, sort_keys=True)
    if args.receipt is not None:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
