#!/usr/bin/env python3
"""Finite, exact query-relative coordinate-width search for WrongType hypervoxels.

DASHI-original algorithm. A frame coordinate has three values C/T/P.
McNamara's Episode 4 assigns first two roles: violated frame, imposed logic.
Additional coordinate names here are analyst-defined and not video quotations.

For an explicitly finite situated domain S, a query Q factors through a
projection pi_I iff equal projected tuples NEVER produce unequal Q answers.
This algorithm enumerates subsets in increasing cardinality and provides
collision witnesses for rejected subsets. It does not decide legal wrongness.
"""
from __future__ import annotations
from itertools import combinations, product
from dataclasses import dataclass
from typing import Any, Callable, Hashable, Iterable, Sequence

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
    observed: dict[tuple[str, ...], tuple[tuple[str, ...], Hashable]] = {}
    for s, answer in zip(states, answers, strict=True):
        key = tuple(s[j] for j in axes)
        if key in observed:
            prior_state, prior_answer = observed[key]
            if prior_answer != answer:
                return Collision(axes, prior_state, s, prior_answer, answer)
        else:
            observed[key] = (s, answer)
    return None


def minimum_width(
    states: Sequence[tuple[str, ...]],
    query: Callable[[tuple[str, ...]], Hashable],
) -> WidthResult:
    if not states:
        raise ValueError("Nonempty finite domain required")
    n = len(states[0])
    if any(len(s) != n or any(x not in MODES for x in s) for s in states):
        raise ValueError("Every state must be a ternary tuple of uniform length")
    if len(set(states)) != len(states):
        raise ValueError("Duplicate states are not allowed")
    answers = [query(s) for s in states]
    failing: list[Collision] = []
    for k in range(n + 1):
        sufficient: list[tuple[int, ...]] = []
        for axes in combinations(range(n), k):
            collision = collision_for_axes(states, answers, axes)
            if collision is None:
                sufficient.append(axes)
            else:
                failing.append(collision)
        if sufficient:
            return WidthResult(k, tuple(sufficient), tuple(failing), len(states))
    raise AssertionError("The identity projection is sufficient on a finite domain")


def main() -> None:
    from argparse import ArgumentParser
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--axes", type=int, default=4)
    parser.add_argument("--query", choices=["identity", "grid", "last", "parity"], default="identity")
    args = parser.parse_args()
    if args.axes < 2 or args.axes > 9:
        parser.error("--axes must be between 2 and 9 for exhaustive evaluation")
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
