#!/usr/bin/env python3
"""Matched causal-pants fabric scan for finite IIT-4 system phi.

The wiring/gluing topology is fixed:

    A[t+1] = C[t]
    B[t+1] = A[t]
    C[t+1] = mu(A[t], B[t])

Only the local 2->1 synthesis operation ``mu`` changes.  This separates
fabric/gluing topology from local gate algebra.

This script computes the finite system-level IIT quantity phi_s (small phi)
by enumerating maximal cause/effect states and directional system partitions.
It does NOT unfold distinctions/relations or compute big-Phi.

For q=3, MIP ordering uses ``affected_connections * log2(q)`` as an explicit
equal-alphabet normalization extension.  The returned unnormalised phi_s is
reported separately and is the main comparison quantity.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import log2
import json

UNITS = (0, 1, 2)
DIRECTIONS = ("in", "out", "both")


def set_partitions(seq):
    seq = list(seq)
    if not seq:
        yield []
        return
    first = seq[0]
    for rest in set_partitions(seq[1:]):
        yield [frozenset([first])] + rest
        for i in range(len(rest)):
            yield rest[:i] + [rest[i] | {first}] + rest[i + 1 :]


def canonical_partition(blocks):
    return tuple(sorted((tuple(sorted(b)) for b in blocks), key=lambda b: (b[0], len(b))))


PARTITIONS = sorted(
    {canonical_partition(p) for p in set_partitions(UNITS) if len(p) >= 2}
)


def cut_sources(partition, directions):
    all_units = set(UNITS)
    blocks = [set(b) for b in partition]
    result = []
    for i, (block, direction) in enumerate(zip(blocks, directions)):
        if direction in ("in", "both"):
            result.append(all_units - block)
        else:
            sources = set()
            for j, (other, other_direction) in enumerate(zip(blocks, directions)):
                if j != i and other_direction in ("out", "both"):
                    sources |= other
            result.append(sources)
    return result


DIRECTIONAL_PARTITIONS = []
for partition in PARTITIONS:
    for directions in product(DIRECTIONS, repeat=len(partition)):
        cuts = cut_sources(partition, directions)
        affected = sum(len(block) * len(cut) for block, cut in zip(partition, cuts))
        if affected:
            DIRECTIONAL_PARTITIONS.append((partition, directions, cuts, affected))


def xor2(a, b):
    return a ^ b


def or2(a, b):
    return int(bool(a) or bool(b))


def and2(a, b):
    return int(bool(a) and bool(b))


def tri_xor(a, b):
    return (a + b) % 3


def step(state, gate):
    a, b, c = state
    return (c, a, gate(a, b))


def states(q):
    return list(product(range(q), repeat=3))


def transition_probability(gate, source, target):
    return Fraction(int(step(source, gate) == target), 1)


def unconstrained_effect(q, gate, target):
    carrier = states(q)
    return sum(
        (transition_probability(gate, source, target) for source in carrier),
        Fraction(),
    ) / len(carrier)


def posterior_cause(q, gate, cause, current):
    denominator = sum(
        (transition_probability(gate, source, current) for source in states(q)),
        Fraction(),
    )
    if denominator == 0:
        return Fraction()
    return transition_probability(gate, cause, current) / denominator


def intrinsic_effect(q, gate, current, effect):
    p = transition_probability(gate, current, effect)
    if p == 0:
        return 0.0
    return float(p) * log2(float(p / unconstrained_effect(q, gate, effect)))


def intrinsic_cause(q, gate, current, cause):
    posterior = posterior_cause(q, gate, cause, current)
    p_forward = transition_probability(gate, cause, current)
    if posterior == 0 or p_forward == 0:
        return 0.0
    return float(posterior) * log2(
        float(p_forward / unconstrained_effect(q, gate, current))
    )


def maximal_states(q, gate, current, side):
    score = intrinsic_effect if side == "effect" else intrinsic_cause
    scored = [(score(q, gate, current, candidate), candidate) for candidate in states(q)]
    best = max(value for value, _ in scored)
    return [candidate for value, candidate in scored if abs(value - best) < 1e-12]


def block_partitioned_probability(q, gate, source, target, block, noised_sources):
    noised_sources = sorted(noised_sources)
    total = q ** len(noised_sources)
    hits = 0
    for replacements in product(range(q), repeat=len(noised_sources)):
        perturbed = list(source)
        for index, value in zip(noised_sources, replacements):
            perturbed[index] = value
        successor = step(tuple(perturbed), gate)
        if tuple(successor[i] for i in block) == tuple(target[i] for i in block):
            hits += 1
    return Fraction(hits, total)


def partitioned_probability(q, gate, source, target, partition, cuts):
    probability = Fraction(1, 1)
    for block, noised_sources in zip(partition, cuts):
        probability *= block_partitioned_probability(
            q, gate, source, target, block, noised_sources
        )
    return probability


def system_phi(q, gate, current):
    best_tie = None
    for cause in maximal_states(q, gate, current, "cause"):
        posterior = posterior_cause(q, gate, cause, current)
        for effect in maximal_states(q, gate, current, "effect"):
            candidates = []
            for partition, directions, cuts, affected in DIRECTIONAL_PARTITIONS:
                p_effect_theta = partitioned_probability(
                    q, gate, current, effect, partition, cuts
                )
                p_cause_theta = partitioned_probability(
                    q, gate, cause, current, partition, cuts
                )

                phi_effect = (
                    float("inf")
                    if p_effect_theta == 0
                    else max(0.0, log2(float(Fraction(1, 1) / p_effect_theta)))
                )
                phi_cause = 0.0
                if posterior != 0:
                    phi_cause = (
                        float("inf")
                        if p_cause_theta == 0
                        else float(posterior)
                        * max(0.0, log2(float(Fraction(1, 1) / p_cause_theta)))
                    )

                phi_s = min(phi_cause, phi_effect)
                normalizer = affected * log2(q)
                relative = phi_s / normalizer
                candidates.append(
                    (
                        relative,
                        -phi_s,
                        phi_s,
                        partition,
                        directions,
                        p_effect_theta,
                        p_cause_theta,
                    )
                )

            candidates.sort(key=lambda row: (row[0], row[1]))
            chosen = candidates[0]
            if best_tie is None or chosen[2] > best_tie[2]:
                best_tie = chosen
    return best_tie


def run():
    experiments = [
        ("binary XOR", 2, xor2),
        ("binary OR", 2, or2),
        ("binary AND", 2, and2),
        ("ternary triXor", 3, tri_xor),
    ]
    summary = []
    states_receipt = []

    for label, q, gate in experiments:
        results = []
        for state in states(q):
            result = system_phi(q, gate, state)
            results.append(result)
            states_receipt.append(
                {
                    "gate": label,
                    "alphabet": q,
                    "state": state,
                    "phi_s_bits": result[2],
                    "mip": result[3],
                    "directions": result[4],
                    "effect_p_theta": str(result[5]),
                    "cause_p_theta": str(result[6]),
                }
            )

        values = [result[2] for result in results]
        summary.append(
            {
                "gate": label,
                "alphabet": q,
                "states_tested": q ** 3,
                "zero_phi_states": sum(abs(value) < 1e-12 for value in values),
                "min_phi_s_bits": min(values),
                "max_phi_s_bits": max(values),
                "distinct_phi_s_bits": sorted({round(value, 12) for value in values}),
                "distinct_mips": len({(result[3], result[4]) for result in results}),
            }
        )

    receipt = {
        "contract": "iit_pants_fabric_matched_gate_scan",
        "fabric": {
            "A_next": "C",
            "B_next": "A",
            "C_next": "mu(A,B)",
            "fixed_across_experiments": True,
        },
        "scope": "finite IIT-4 system phi_s prototype; not full big-Phi",
        "ternary_mip_normalization": "affected_connections * log2(q), explicit equal-alphabet extension assumption",
        "summary": summary,
        "states": states_receipt,
    }
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    run()
