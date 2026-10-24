#!/usr/bin/env python3
"""Small exact finite IIT-4 reference evaluator.

Scope
-----
This module implements the finite system-level IIT-4 calculation used by the
DASHI integration fixtures.  It deliberately keeps two named formalisms:

* ``IIT_4_0_2023``: Albantakis et al. (2023), system phi is
  ``min(phi_c, phi_e)`` at the normalized minimum directional partition.
* ``IIT_4_0_2026``: the same MIP search, followed by the Mayner et al. (2026)
  intrinsic-information requirement ``min(phi_c, phi_e, ii(s))``.

The model exposes a factored node transition probability function.  This is
important: directional cuts causally marginalize selected *inputs to target
units* independently; they are not graph-cut counts and they never rewrite a
local gate law.

This is an executable reference and receipt generator, not an Agda kernel
proof and not the full distinction/relation unfolding of big-Phi.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import log2
from typing import Callable, Iterable, Sequence

IIT4_2023 = "IIT_4_0_2023"
IIT4_2026 = "IIT_4_0_2026"
FORMALISMS = (IIT4_2023, IIT4_2026)
DIRECTIONS = ("in", "out", "both")
State = tuple[int, ...]


def positive_part(x: float) -> float:
    return max(0.0, x)


def _fraction_float(x: Fraction) -> float:
    return x.numerator / x.denominator


def _log_ratio(p: Fraction, q: Fraction) -> float:
    if p <= 0:
        return 0.0
    if q <= 0:
        return float("inf")
    return log2(_fraction_float(p / q))


@dataclass(frozen=True)
class FiniteCausalModel:
    """Factored finite transition model.

    ``node_probability(source, target_unit, target_value)`` returns the exact
    probability for one target unit after intervening on the complete source
    state.  Target units are conditionally independent given the intervention,
    matching the factored TPM interface used by IIT implementations.
    """

    alphabet_sizes: tuple[int, ...]
    node_probability: Callable[[State, int, int], Fraction]
    label: str = "finite-causal-model"

    @property
    def unit_count(self) -> int:
        return len(self.alphabet_sizes)

    @property
    def states(self) -> tuple[State, ...]:
        return tuple(product(*(range(q) for q in self.alphabet_sizes)))

    def validate_state(self, state: State) -> None:
        if len(state) != self.unit_count:
            raise ValueError("state arity does not match model")
        for value, q in zip(state, self.alphabet_sizes):
            if value < 0 or value >= q:
                raise ValueError("state value outside declared alphabet")

    def transition_probability(self, source: State, target: State) -> Fraction:
        self.validate_state(source)
        self.validate_state(target)
        p = Fraction(1, 1)
        for unit, value in enumerate(target):
            term = self.node_probability(source, unit, value)
            if term < 0 or term > 1:
                raise ValueError("node probability outside [0,1]")
            p *= term
        return p


def deterministic_model(
    alphabet_size: int,
    unit_count: int,
    step: Callable[[State], State],
    *,
    label: str = "deterministic-model",
) -> FiniteCausalModel:
    if alphabet_size < 2:
        raise ValueError("alphabet size must be at least two")

    def node_probability(source: State, unit: int, value: int) -> Fraction:
        target = step(source)
        if len(target) != unit_count:
            raise ValueError("step returned wrong state arity")
        return Fraction(int(target[unit] == value), 1)

    return FiniteCausalModel(
        alphabet_sizes=(alphabet_size,) * unit_count,
        node_probability=node_probability,
        label=label,
    )


def recurrent_three_cell_step(
    gate: Callable[[int, int], int]
) -> Callable[[State], State]:
    """Fixed recurrent fibre fabric: A'=C, B'=A, C'=mu(A,B)."""

    def step(state: State) -> State:
        a, b, c = state
        return c, a, gate(a, b)

    return step


def feedforward_three_cell_step(
    gate: Callable[[int, int], int]
) -> Callable[[State], State]:
    """Feed-forward control: A and B persist and only synthesize C."""

    def step(state: State) -> State:
        a, b, _c = state
        return a, b, gate(a, b)

    return step


def _set_partitions(seq: Sequence[int]):
    seq = list(seq)
    if not seq:
        yield []
        return
    first = seq[0]
    for rest in _set_partitions(seq[1:]):
        yield [frozenset([first])] + rest
        for index in range(len(rest)):
            yield rest[:index] + [rest[index] | {first}] + rest[index + 1 :]


def _canonical_partition(blocks: Iterable[Iterable[int]]) -> tuple[tuple[int, ...], ...]:
    return tuple(
        sorted(
            (tuple(sorted(block)) for block in blocks),
            key=lambda block: (block[0], len(block), block),
        )
    )


def _cut_sources(
    partition: tuple[tuple[int, ...], ...], directions: tuple[str, ...]
) -> tuple[tuple[int, ...], ...]:
    universe = set(unit for block in partition for unit in block)
    blocks = [set(block) for block in partition]
    cut_sets: list[tuple[int, ...]] = []
    for index, (block, direction) in enumerate(zip(blocks, directions)):
        if direction in ("in", "both"):
            cut = universe - block
        elif direction == "out":
            cut: set[int] = set()
            for other_index, (other, other_direction) in enumerate(
                zip(blocks, directions)
            ):
                if other_index != index and other_direction in ("out", "both"):
                    cut |= other
        else:
            raise ValueError(f"unknown cut direction: {direction}")
        cut_sets.append(tuple(sorted(cut)))
    return tuple(cut_sets)


def directional_partitions(unit_count: int) -> tuple[dict, ...]:
    """Enumerate IIT directional partitions of all units into >=2 parts."""
    if unit_count < 2:
        return ()
    partitions = sorted(
        {
            _canonical_partition(parts)
            for parts in _set_partitions(tuple(range(unit_count)))
            if len(parts) >= 2
        },
        key=lambda p: (len(p), p),
    )
    result = []
    for partition in partitions:
        for directions in product(DIRECTIONS, repeat=len(partition)):
            cuts = _cut_sources(partition, directions)
            affected = sum(
                len(block) * len(cut)
                for block, cut in zip(partition, cuts)
            )
            if affected == 0:
                continue
            result.append(
                {
                    "parts": partition,
                    "directions": tuple(directions),
                    "cut_sources": cuts,
                    "affected_connection_count": affected,
                }
            )
    return tuple(result)


def unconstrained_effect_probability(
    model: FiniteCausalModel, target: State
) -> Fraction:
    return sum(
        (model.transition_probability(source, target) for source in model.states),
        Fraction(0, 1),
    ) / len(model.states)


def cause_probability(
    model: FiniteCausalModel, cause: State, current: State
) -> Fraction:
    numerator = model.transition_probability(cause, current)
    denominator = sum(
        (model.transition_probability(source, current) for source in model.states),
        Fraction(0, 1),
    )
    if denominator == 0:
        return Fraction(0, 1)
    return numerator / denominator


def intrinsic_effect_specification(
    model: FiniteCausalModel, current: State, effect: State
) -> float:
    constrained = model.transition_probability(current, effect)
    unconstrained = unconstrained_effect_probability(model, effect)
    if constrained == 0 or unconstrained == 0:
        return 0.0
    return _fraction_float(constrained) * _log_ratio(constrained, unconstrained)


def intrinsic_cause_specification(
    model: FiniteCausalModel, current: State, cause: State
) -> float:
    selectivity = cause_probability(model, cause, current)
    forward = model.transition_probability(cause, current)
    unconstrained_current = unconstrained_effect_probability(model, current)
    if selectivity == 0 or forward == 0 or unconstrained_current == 0:
        return 0.0
    return _fraction_float(selectivity) * _log_ratio(forward, unconstrained_current)


def maximal_specified_states(
    model: FiniteCausalModel, current: State, direction: str
) -> tuple[dict, ...]:
    if direction == "effect":
        scored = [
            (intrinsic_effect_specification(model, current, state), state)
            for state in model.states
        ]
    elif direction == "cause":
        scored = [
            (intrinsic_cause_specification(model, current, state), state)
            for state in model.states
        ]
    else:
        raise ValueError("direction must be cause or effect")
    maximum = max(score for score, _state in scored)
    return tuple(
        {"state": state, "intrinsic_specification": score}
        for score, state in scored
        if abs(score - maximum) < 1.0e-12
    )


def _marginalized_node_probability(
    model: FiniteCausalModel,
    source: State,
    target_unit: int,
    target_value: int,
    cut_source_units: Sequence[int],
) -> Fraction:
    cut_source_units = tuple(sorted(set(cut_source_units)))
    if not cut_source_units:
        return model.node_probability(source, target_unit, target_value)
    ranges = [range(model.alphabet_sizes[index]) for index in cut_source_units]
    total = 1
    for index in cut_source_units:
        total *= model.alphabet_sizes[index]
    probability = Fraction(0, 1)
    for replacement in product(*ranges):
        intervened = list(source)
        for index, value in zip(cut_source_units, replacement):
            intervened[index] = value
        probability += model.node_probability(
            tuple(intervened), target_unit, target_value
        )
    return probability / total


def partitioned_effect_probability(
    model: FiniteCausalModel,
    source: State,
    target: State,
    partition: dict,
) -> Fraction:
    p = Fraction(1, 1)
    for block, cut_sources in zip(
        partition["parts"], partition["cut_sources"]
    ):
        for target_unit in block:
            p *= _marginalized_node_probability(
                model,
                source,
                target_unit,
                target[target_unit],
                cut_sources,
            )
    return p


def _integrated_effect(
    model: FiniteCausalModel,
    current: State,
    effect: State,
    partition: dict,
) -> float:
    selectivity = model.transition_probability(current, effect)
    partitioned = partitioned_effect_probability(model, current, effect, partition)
    if selectivity == 0:
        return 0.0
    return _fraction_float(selectivity) * positive_part(
        _log_ratio(selectivity, partitioned)
    )


def _integrated_cause(
    model: FiniteCausalModel,
    current: State,
    cause: State,
    partition: dict,
) -> float:
    selectivity = cause_probability(model, cause, current)
    unpartitioned_forward = model.transition_probability(cause, current)
    partitioned_forward = partitioned_effect_probability(
        model, cause, current, partition
    )
    if selectivity == 0 or unpartitioned_forward == 0:
        return 0.0
    return _fraction_float(selectivity) * positive_part(
        _log_ratio(unpartitioned_forward, partitioned_forward)
    )


def _intrinsic_differentiation(probability: Fraction) -> float:
    """Specified-state surprisal used by the 2026 intrinsic-information cap."""
    if probability <= 0:
        return 0.0
    return -log2(_fraction_float(probability))


def _serializable_partition(partition: dict) -> dict:
    return {
        "parts": [list(block) for block in partition["parts"]],
        "directions": list(partition["directions"]),
        "cut_sources": [list(cut) for cut in partition["cut_sources"]],
        "affected_connection_count": partition["affected_connection_count"],
    }


def system_phi(
    model: FiniteCausalModel,
    current: State,
    *,
    formalism: str = IIT4_2023,
) -> dict:
    """Evaluate finite system phi and return a machine-readable receipt.

    The MIP is selected on normalized 2023 integration.  Under the 2026
    formalism the intrinsic-information requirement is applied only after that
    MIP has been selected, matching the current versioned implementation.
    """
    if formalism not in FORMALISMS:
        raise ValueError(f"unsupported IIT formalism: {formalism}")
    model.validate_state(current)

    cause_candidates = maximal_specified_states(model, current, "cause")
    effect_candidates = maximal_specified_states(model, current, "effect")
    partitions = directional_partitions(model.unit_count)
    if not partitions:
        return {
            "formalism": formalism,
            "model": model.label,
            "current_state": list(current),
            "phi_s": 0.0,
            "phi_s_2023": 0.0,
            "intrinsic_information": 0.0,
            "reason": "fewer than two units: no nontrivial directional partition",
            "mip": None,
        }

    tie_results = []
    for cause_record in cause_candidates:
        cause = cause_record["state"]
        cause_selectivity = cause_probability(model, cause, current)
        cause_diff = _intrinsic_differentiation(cause_selectivity)
        for effect_record in effect_candidates:
            effect = effect_record["state"]
            effect_selectivity = model.transition_probability(current, effect)
            effect_diff = _intrinsic_differentiation(effect_selectivity)

            partition_results = []
            for partition in partitions:
                phi_c = _integrated_cause(model, current, cause, partition)
                phi_e = _integrated_effect(model, current, effect, partition)
                phi_2023 = min(phi_c, phi_e)
                normalizer = partition["affected_connection_count"]
                normalized = phi_2023 / normalizer
                partition_results.append(
                    {
                        "partition": partition,
                        "phi_c": phi_c,
                        "phi_e": phi_e,
                        "phi_s_2023": phi_2023,
                        "normalized_phi": normalized,
                        "partitioned_cause_forward_probability": partitioned_effect_probability(
                            model, cause, current, partition
                        ),
                        "partitioned_effect_probability": partitioned_effect_probability(
                            model, current, effect, partition
                        ),
                    }
                )

            # Minimal normalized integration; in a normalization tie retain the
            # larger unnormalized value, consistent with the exclusion intent.
            partition_results.sort(
                key=lambda row: (row["normalized_phi"], -row["phi_s_2023"])
            )
            mip = partition_results[0]
            intrinsic_information = min(
                positive_part(cause_record["intrinsic_specification"]),
                positive_part(effect_record["intrinsic_specification"]),
                positive_part(cause_diff),
                positive_part(effect_diff),
            )
            phi_final = mip["phi_s_2023"]
            if formalism == IIT4_2026:
                phi_final = min(phi_final, intrinsic_information)

            tie_results.append(
                {
                    "cause_state": cause,
                    "effect_state": effect,
                    "cause_intrinsic_specification": cause_record[
                        "intrinsic_specification"
                    ],
                    "effect_intrinsic_specification": effect_record[
                        "intrinsic_specification"
                    ],
                    "cause_intrinsic_differentiation": cause_diff,
                    "effect_intrinsic_differentiation": effect_diff,
                    "intrinsic_information": intrinsic_information,
                    "phi_s": phi_final,
                    "phi_s_2023": mip["phi_s_2023"],
                    "mip": mip,
                }
            )

    # Keep all maximal-specification ties alive through partition analysis, then
    # select the reading with maximal irreducibility.  The receipt records the
    # candidate count so a stronger tie cascade can replace this policy without
    # silently changing historical runs.
    tie_results.sort(key=lambda row: (-row["phi_s"], -row["phi_s_2023"]))
    chosen = tie_results[0]
    mip = chosen["mip"]
    return {
        "formalism": formalism,
        "model": model.label,
        "current_state": list(current),
        "cause_state": list(chosen["cause_state"]),
        "effect_state": list(chosen["effect_state"]),
        "cause_intrinsic_specification": chosen[
            "cause_intrinsic_specification"
        ],
        "effect_intrinsic_specification": chosen[
            "effect_intrinsic_specification"
        ],
        "cause_intrinsic_differentiation": chosen[
            "cause_intrinsic_differentiation"
        ],
        "effect_intrinsic_differentiation": chosen[
            "effect_intrinsic_differentiation"
        ],
        "intrinsic_information": chosen["intrinsic_information"],
        "phi_c": mip["phi_c"],
        "phi_e": mip["phi_e"],
        "phi_s_2023": chosen["phi_s_2023"],
        "phi_s": chosen["phi_s"],
        "mip": {
            **_serializable_partition(mip["partition"]),
            "normalized_phi": mip["normalized_phi"],
            "partitioned_cause_forward_probability": str(
                mip["partitioned_cause_forward_probability"]
            ),
            "partitioned_effect_probability": str(
                mip["partitioned_effect_probability"]
            ),
        },
        "specified_state_tie_candidates": len(tie_results),
    }
