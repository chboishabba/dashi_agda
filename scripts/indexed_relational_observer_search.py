#!/usr/bin/env python3
"""Generic finite-domain consumer factorisation and minimum observer width.

DASHI Core, not a McNamara/369 legal semantics owner.

Inputs: explicitly enumerated finite states, named observations on any
hashable carriers, a consumer query. An observer subset is sufficient iff
every observed fibre has a constant consumer outcome. Rejected subsets
carry concrete same-view/different-answer witnesses.

IMPORTANT: Exhaustive only over the supplied finite domain. Sampling
points of a wave or continuous field cannot prove continuum sufficiency.
The source-level Agda factorisation/collision proof carries the universal
statement when a valid mathematical witness is available.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product
from typing import Callable, Hashable, Iterable, Mapping, Sequence, TypeVar

State = TypeVar("State")
Answer = TypeVar("Answer", bound=Hashable)
Observation = Callable[[State], Hashable]


@dataclass(frozen=True)
class Collision:
    observer_names: tuple[str, ...]
    left_state: object
    right_state: object
    same_view: tuple[Hashable, ...]
    left_answer: Hashable
    right_answer: Hashable


@dataclass(frozen=True)
class MinimumObserverResult:
    width: int
    sufficient_observers: tuple[tuple[str, ...], ...]
    rejected: tuple[Collision, ...]
    finite_domain_size: int

    @property
    def k(self) -> int:
        return self.width


def finite_product(alphabets: Sequence[Sequence[Hashable]]) -> Iterable[tuple[Hashable, ...]]:
    """Independent, heterogeneous finite carriers: cardinality = product of arities."""
    if any(not alphabet for alphabet in alphabets):
        raise ValueError("Every axis requires a nonempty alphabet")
    return product(*alphabets)


def first_collision(
    states: Sequence[State],
    query: Callable[[State], Hashable],
    observers: Mapping[str, Observation[State]],
    names: tuple[str, ...],
) -> Collision | None:
    seen: dict[tuple[Hashable, ...], tuple[State, Hashable]] = {}
    for state in states:
        view = tuple(observers[name](state) for name in names)
        answer = query(state)
        if view in seen:
            earlier, earlier_answer = seen[view]
            if answer != earlier_answer:
                return Collision(names, earlier, state, view, earlier_answer, answer)
        else:
            seen[view] = (state, answer)
    return None


def minimum_observers(
    states: Sequence[State],
    query: Callable[[State], Hashable],
    observers: Mapping[str, Observation[State]],
    *,
    require_unique_states: bool = True,
) -> MinimumObserverResult | None:
    if not states:
        raise ValueError("The finite evaluation domain must not be empty")
    if require_unique_states and len(set(states)) != len(states):
        raise ValueError("Finite states must be unique and hashable")
    if len(set(observers)) != len(observers):
        raise ValueError("Observer names must be unique")
    names = tuple(observers)
    rejected: list[Collision] = []
    for k in range(len(names) + 1):
        accepted: list[tuple[str, ...]] = []
        for subset in combinations(names, k):
            failure = first_collision(states, query, observers, subset)
            if failure is None:
                accepted.append(subset)
            else:
                rejected.append(failure)
        if accepted:
            return MinimumObserverResult(k, tuple(accepted), tuple(rejected), len(states))
    # No observer set sufficient for the supplied consumer. This is
    # possible when all observers lose a relevant distinction.
    return None


def coordinate_observers(n: int) -> dict[str, Observation[tuple[Hashable, ...]]]:
    if n < 0:
        raise ValueError("Axis count must be nonnegative")
    return {
        f"axis:{i}": (lambda state, index=i: state[index])
        for i in range(n)
    }


def minimum_coordinate_width(
    states: Sequence[tuple[Hashable, ...]],
    query: Callable[[tuple[Hashable, ...]], Hashable],
) -> MinimumObserverResult | None:
    if not states:
        raise ValueError("Finite domain required")
    n = len(states[0])
    if any(len(s) != n for s in states):
        raise ValueError("All coordinates must share a fixed arity")
    return minimum_observers(states, query, coordinate_observers(n))


def main() -> None:
    from argparse import ArgumentParser
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--axes", type=int, default=4)
    parser.add_argument("--arity", type=int, default=3)
    parser.add_argument("--query", choices=("identity", "first-two", "last", "constant"), default="first-two")
    args = parser.parse_args()
    if args.axes < 1 or args.arity < 1 or args.arity ** args.axes > 100000:
        parser.error("Requires positive axes and arity, with no more than 100,000 states")
    domain = list(finite_product([tuple(range(args.arity))] * args.axes))
    if args.query == "identity":
        query = lambda s: s
    elif args.query == "first-two":
        query = lambda s: s[:2]
    elif args.query == "last":
        query = lambda s: s[-1]
    else:
        query = lambda s: 0
    result = minimum_coordinate_width(domain, query)
    print({"domain": len(domain),
           "minimum_width": None if result is None else result.width,
           "minimal_observers": None if result is None else result.sufficient_observers,
           "rejected_subsets": None if result is None else len(result.rejected)})


if __name__ == "__main__":
    main()
