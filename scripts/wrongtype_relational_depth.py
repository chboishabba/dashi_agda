#!/usr/bin/env python3
"""Backward-compatible three-mode WrongType adapter to generic observer search.

McNamara ep. 4 describes Care/Transaction/Power on two source-defined
axes. All coordinate-width and factorisation algorithms are owned by
scripts/indexed_relational_observer_search.py. Extra ternary axes are
DASHI extensions, not directly attributable to McNamara.

A finite table gives domain-relative certificates, not universal legal
or analytical conclusions.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Callable, Hashable, Iterable, Sequence

from scripts.indexed_relational_observer_search import (
    first_collision, minimum_coordinate_width, coordinate_observers
)

MODES = ("C", "T", "P")


@dataclass(frozen=True)
class Collision:
    axes: tuple[int, ...]
    left: tuple[str, ...]
    right: tuple[str, ...]
    left_answer: Hashable
    right_answer: Hashable


@dataclass(frozen=True)
class WidthResult:
    width: int
    sufficient_sets: tuple[tuple[int, ...], ...]
    failing: tuple[Collision, ...]
    exhaustive_domain_size: int


def cube(n: int) -> Iterable[tuple[str, ...]]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    return product(MODES, repeat=n)


def collision_for_axes(
    states: Sequence[tuple[str, ...]],
    answers: Sequence[Hashable],
    axes: tuple[int, ...],
) -> Collision | None:
    if len(states) != len(answers):
        raise ValueError("Answer table must match finite domain")
    answer_lookup = dict(zip(states, answers, strict=True))
    if len(answer_lookup) != len(states):
        raise ValueError("Finite states must be unique")
    names = tuple(f"axis:{i}" for i in axes)
    witness = first_collision(
        states, answer_lookup.__getitem__, coordinate_observers(len(states[0])),
        names,
    )
    if witness is None:
        return None
    return Collision(axes, witness.left_state, witness.right_state,
                     witness.left_answer, witness.right_answer)


def minimum_width(
    states: Sequence[tuple[str, ...]],
    query: Callable[[tuple[str, ...]], Hashable],
) -> WidthResult:
    if not states:
        raise ValueError("Nonempty finite domain required")
    n = len(states[0])
    if any(len(s) != n or any(x not in MODES for x in s) for s in states):
        raise ValueError("Expected fixed-length three-mode tuples")
    result = minimum_coordinate_width(states, query)
    if result is None:
        raise AssertionError("Full coordinate projection should be sufficient")
    failing = tuple(
        Collision(
            tuple(int(name.removeprefix("axis:")) for name in witness.observer_names),
            witness.left_state, witness.right_state,
            witness.left_answer, witness.right_answer,
        )
        for witness in result.rejected
    )
    return WidthResult(
        result.width,
        tuple(tuple(int(name.removeprefix("axis:")) for name in choice)
              for choice in result.sufficient_observers),
        failing,
        result.finite_domain_size,
    )


def main() -> None:
    from argparse import ArgumentParser
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--axes", type=int, default=4)
    parser.add_argument("--query", choices=("identity", "grid", "last", "parity"), default="identity")
    args = parser.parse_args()
    if not 2 <= args.axes <= 9:
        parser.error("--axes must be between 2 and 9")
    states = list(cube(args.axes))
    if args.query == "identity":
        query = lambda s: s
    elif args.query == "grid":
        query = lambda s: s[:2]
    elif args.query == "last":
        query = lambda s: s[-1]
    else:
        query = lambda s: sum(x == "P" for x in s) % 2
    result = minimum_width(states, query)
    print({
        "axes": args.axes,
        "query": args.query,
        "width": result.width,
        "sufficient_subsets": result.sufficient_sets,
        "rejected_subset_witnesses": len(result.failing),
        "domain_size": result.exhaustive_domain_size,
    })


if __name__ == "__main__":
    main()
