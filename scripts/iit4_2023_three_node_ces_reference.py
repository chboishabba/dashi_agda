#!/usr/bin/env python3
"""Golden-calibrated finite IIT-4.0-2023 CES reference for 3 binary nodes.

Purpose
-------
PyPhi remains the external numerical authority.  The current execution runtime
cannot install the PyPhi package, but the pinned upstream source and golden XOR
fixture are available from GitHub.  This script therefore implements only the
small three-binary-node slice needed by the DASHI matched higher-order test,
following the current PyPhi source formulas and refusing promotion unless it
reproduces the upstream canonical XOR golden fixture exactly at state 000.

Pinned upstream source used when this reference was written:
  repository: https://github.com/wmayner/pyphi
  source commit: 134a8f31b49db512322465ed3ba5da7194d362fd
  golden: test/data/golden/v1/xor_iit4_2023.json

The golden fixture records, for the fully connected 3-node XOR substrate at
000 under IIT_4_0_2023 + GENERALIZED_INTRINSIC_DIFFERENCE:
  system phi_s       = 1.5
  distinctions       = 4, phis 0.5, 1.0, 0.5, 0.5
  relations          = 15
  sum relation phi   = 7.0
  big Phi            = 9.5

Implemented source-derived ingredients:
  * cause/effect repertoires and forward repertoires;
  * generalized intrinsic difference s_i log2(f_i/f_part_i);
  * JOINT_PARTITION_ALL mechanism/purview partitions;
  * IIT-4 connection-count MIP normalization, then raw-phi tie preference;
  * maximal-purview exclusion by raw phi;
  * congruence with the system cause/effect state;
  * IIT-4 relation overlap and phi formula;
  * big Phi = sum distinction phi + sum relation phi.

Scope boundary
--------------
This is a finite, source-derived regression reference, not a replacement for
PyPhi and not an Agda theorem.  It is intentionally specialized to deterministic
3-node binary systems and the IIT_4_0_2023 formalism.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from itertools import combinations, permutations, product
from math import log2
from pathlib import Path

N = 3
NODES = tuple(range(N))
STATES = tuple(product((0, 1), repeat=N))
DIRECTIONS = ("in", "out", "both")
SOURCE_COMMIT = "134a8f31b49db512322465ed3ba5da7194d362fd"
GOLDEN_BIG_PHI = 9.5


def xor_step(state):
    a, b, c = state
    return b ^ c, a ^ c, a ^ b


def triadic_step(state):
    a, b, c = state
    return b ^ c, a ^ c, (a ^ b) ^ (a & b & c)


def nonempty_powerset(seq):
    seq = tuple(seq)
    return [p for size in range(1, len(seq) + 1) for p in combinations(seq, size)]


def node_probability(step, source, unit, value):
    return Fraction(int(step(source)[unit] == value), 1)


def forward_effect(step, current, mechanism, purview, purview_state):
    probability = Fraction(1, 1)
    for target, value in zip(purview, purview_state):
        free = tuple(i for i in NODES if i not in mechanism)
        marginal = Fraction(0, 1)
        for values in product((0, 1), repeat=len(free)):
            source = list(current)
            for i, v in zip(free, values):
                source[i] = v
            marginal += node_probability(step, tuple(source), target, value)
        probability *= marginal / (2 ** len(free))
    return probability


def forward_cause(step, current, mechanism, purview, purview_state):
    probability = Fraction(1, 1)
    for target in mechanism:
        target_value = current[target]
        free = tuple(i for i in NODES if i not in purview)
        marginal = Fraction(0, 1)
        for values in product((0, 1), repeat=len(free)):
            source = [0] * N
            for i, v in zip(purview, purview_state):
                source[i] = v
            for i, v in zip(free, values):
                source[i] = v
            marginal += node_probability(step, tuple(source), target, target_value)
        probability *= marginal / (2 ** len(free))
    return probability


def forward_probability(step, current, direction, mechanism, purview, state):
    if direction == "effect":
        return forward_effect(step, current, mechanism, purview, state)
    return forward_cause(step, current, mechanism, purview, state)


def repertoire(step, current, direction, mechanism, purview):
    states = tuple(product((0, 1), repeat=len(purview)))
    forward = [
        forward_probability(step, current, direction, mechanism, purview, state)
        for state in states
    ]
    if direction == "effect":
        return dict(zip(states, forward))
    denominator = sum(forward, Fraction(0, 1))
    return {
        state: (value / denominator if denominator else Fraction(0, 1))
        for state, value in zip(states, forward)
    }


def unconstrained_forward(step, current, direction, mechanism, purview):
    states = tuple(product((0, 1), repeat=len(purview)))
    if direction == "effect":
        return {
            state: forward_effect(step, current, (), purview, state)
            for state in states
        }
    forward = [forward_cause(step, current, mechanism, purview, state) for state in states]
    mean = sum(forward, Fraction(0, 1)) / len(states)
    return {state: mean for state in states}


def pmi(forward, comparison):
    # Current PyPhi pointwise_mutual_information_vector returns zero whenever
    # the ratio is undefined (forward == 0 or comparison == 0).
    if forward <= 0 or comparison <= 0:
        return 0.0
    return log2(float(forward / comparison))


def intrinsic_specification_states(step, current, direction, mechanism, purview):
    selectivity = repertoire(step, current, direction, mechanism, purview)
    unconstrained = unconstrained_forward(step, current, direction, mechanism, purview)
    scores = {}
    for state, weight in selectivity.items():
        forward = forward_probability(step, current, direction, mechanism, purview, state)
        scores[state] = float(weight) * pmi(forward, unconstrained[state])
    maximum = max(scores.values())
    return (
        tuple(state for state, value in scores.items() if abs(value - maximum) < 1e-12),
        scores,
        selectivity,
    )


def _set_partitions(seq):
    seq = list(seq)
    if not seq:
        yield []
        return
    first = seq[0]
    for rest in _set_partitions(seq[1:]):
        yield [[first]] + [block[:] for block in rest]
        for index in range(len(rest)):
            updated = [block[:] for block in rest]
            updated[index] = [first] + updated[index]
            yield updated


def _canonical_partition(partition):
    return tuple(sorted((tuple(sorted(block)) for block in partition), key=lambda b: (b[0], len(b), b)))


def set_partitions(seq):
    return sorted({_canonical_partition(p) for p in _set_partitions(seq)}, key=lambda p: (len(p), p))


def joint_partitions(mechanism, purview):
    """Finite equivalent of current PyPhi JOINT_PARTITION_ALL for n <= 3."""
    output = []
    seen = set()
    for mechanism_partition in set_partitions(mechanism):
        mechanism_parts = [tuple(part) for part in mechanism_partition] + [()]
        count = len(mechanism_parts)
        max_purview_parts = min(len(purview), count)
        for k in range(1, max_purview_parts + 1):
            for purview_partition in set_partitions(purview):
                if len(purview_partition) != k:
                    continue
                purview_parts = [tuple(part) for part in purview_partition] + [()] * (count - k)
                for permuted in set(permutations(purview_parts)):
                    parts = tuple(zip(mechanism_parts, permuted))
                    if parts[0][0] == tuple(mechanism) and parts[0][1]:
                        continue
                    if sum(bool(m) and not p for m, p in parts) > 1:
                        continue
                    key = tuple(sorted(parts, key=lambda part: (part[0], part[1])))
                    if key in seen:
                        continue
                    seen.add(key)
                    output.append(parts)
    return tuple(output)


def partitioned_forward(step, current, direction, mechanism, purview, state, partition):
    state_map = dict(zip(purview, state))
    result = Fraction(1, 1)
    for mechanism_part, purview_part in partition:
        substate = tuple(state_map[i] for i in purview_part)
        result *= forward_probability(
            step, current, direction, mechanism_part, purview_part, substate
        )
    return result


def connections_cut(mechanism, purview, partition):
    total = len(mechanism) * len(purview)
    retained = sum(len(m) * len(p) for m, p in partition)
    return total - retained


def mip(step, current, direction, mechanism, purview):
    specified, specification_scores, selectivity = intrinsic_specification_states(
        step, current, direction, mechanism, purview
    )
    per_state = []
    partitions = joint_partitions(mechanism, purview)
    for state in specified:
        forward = forward_probability(step, current, direction, mechanism, purview, state)
        weight = selectivity[state]
        rows = []
        for partition in partitions:
            partitioned = partitioned_forward(
                step, current, direction, mechanism, purview, state, partition
            )
            phi = float(weight) * pmi(forward, partitioned)
            cuts = connections_cut(mechanism, purview, partition)
            normalized = phi / cuts if cuts else float("inf")
            rows.append((normalized, -phi, phi, partition))
        rows.sort(key=lambda row: (row[0], row[1]))
        winner = rows[0]
        per_state.append(
            {
                "state": state,
                "intrinsic_specification": specification_scores[state],
                "phi": winner[2],
                "normalized_phi": winner[0],
                "partition": winner[3],
            }
        )
    # IIT-4 state tie resolution defaults to maximal raw phi after intrinsic
    # specification has tied the candidate states.
    maximum_phi = max(row["phi"] for row in per_state)
    return tuple(row for row in per_state if abs(row["phi"] - maximum_phi) < 1e-12)


def mice(step, current, direction, mechanism):
    candidates = []
    for purview in nonempty_powerset(NODES):
        for row in mip(step, current, direction, mechanism, purview):
            candidates.append({**row, "purview": purview})
    maximum = max(row["phi"] for row in candidates)
    # IIT-4 default purview resolution is PHI; retain the tied readings so
    # structure-level congruence can resolve them compositionally.
    return tuple(row for row in candidates if abs(row["phi"] - maximum) < 1e-12)


# ---- system-level specified-state / phi_s support for congruence ------------

def transition(step, source, target):
    return Fraction(int(step(source) == target), 1)


def cause_probability(step, cause, current):
    denominator = sum((transition(step, source, current) for source in STATES), Fraction(0, 1))
    if denominator == 0:
        return Fraction(0, 1)
    return transition(step, cause, current) / denominator


def _system_set_partitions(seq):
    return set_partitions(seq)


def directional_partitions():
    universe = set(NODES)
    output = []
    for partition in _system_set_partitions(NODES):
        if len(partition) < 2:
            continue
        blocks = [set(block) for block in partition]
        for directions in product(DIRECTIONS, repeat=len(blocks)):
            cuts = []
            for index, (block, direction) in enumerate(zip(blocks, directions)):
                if direction in ("in", "both"):
                    cut = universe - block
                else:
                    cut = set()
                    for other_index, (other, other_direction) in enumerate(zip(blocks, directions)):
                        if other_index != index and other_direction in ("out", "both"):
                            cut |= other
                cuts.append(tuple(sorted(cut)))
            affected = sum(len(block) * len(cut) for block, cut in zip(blocks, cuts))
            if affected:
                output.append((partition, tuple(cuts), affected))
    return tuple(output)


SYSTEM_PARTITIONS = directional_partitions()


def marginalized_node_probability(step, source, target_unit, target_value, cut_sources):
    cut_sources = tuple(sorted(set(cut_sources)))
    if not cut_sources:
        return node_probability(step, source, target_unit, target_value)
    total = Fraction(0, 1)
    for values in product((0, 1), repeat=len(cut_sources)):
        intervened = list(source)
        for index, value in zip(cut_sources, values):
            intervened[index] = value
        total += node_probability(step, tuple(intervened), target_unit, target_value)
    return total / (2 ** len(cut_sources))


def partitioned_system_probability(step, source, target, partition, cuts):
    result = Fraction(1, 1)
    for block, cut_sources in zip(partition, cuts):
        for unit in block:
            result *= marginalized_node_probability(
                step, source, unit, target[unit], cut_sources
            )
    return result


def system_phi_reading(step, current, cause, effect):
    cause_selectivity = cause_probability(step, cause, current)
    rows = []
    for partition, cuts, affected in SYSTEM_PARTITIONS:
        partitioned_effect = partitioned_system_probability(step, current, effect, partition, cuts)
        partitioned_cause = partitioned_system_probability(step, cause, current, partition, cuts)
        phi_e = 0.0 if partitioned_effect == 0 else max(0.0, log2(float(Fraction(1, 1) / partitioned_effect)))
        phi_c = (
            0.0
            if cause_selectivity == 0 or partitioned_cause == 0
            else float(cause_selectivity) * max(0.0, log2(float(Fraction(1, 1) / partitioned_cause)))
        )
        phi = min(phi_c, phi_e)
        rows.append((phi / affected, -phi, phi))
    rows.sort()
    return rows[0][2]


def system_state_specification(step, current):
    effect = step(current)
    predecessors = tuple(state for state in STATES if step(state) == current)
    if not predecessors:
        return (), (effect,), 0.0
    scored = [(system_phi_reading(step, current, cause, effect), cause) for cause in predecessors]
    maximum = max(value for value, _ in scored)
    causes = tuple(cause for value, cause in scored if abs(value - maximum) < 1e-12)
    return causes, (effect,), maximum


def congruent(reading, system_states):
    purview = reading["purview"]
    state = reading["state"]
    return any(tuple(system_state[i] for i in purview) == state for system_state in system_states)


def unit_states(reading):
    return frozenset(zip(reading["purview"], reading["state"]))


def relation_summary(distinctions):
    for distinction in distinctions:
        distinction["cause_units"] = unit_states(distinction["cause"])
        distinction["effect_units"] = unit_states(distinction["effect"])
        distinction["purview_union"] = distinction["cause_units"] | distinction["effect_units"]

    relations = []
    for index, distinction in enumerate(distinctions):
        overlap = distinction["cause_units"] & distinction["effect_units"]
        if overlap:
            phi = len(overlap) * distinction["phi"] / len(distinction["purview_union"])
            if phi > 1e-12:
                relations.append(((index,), overlap, phi))

    for degree in range(2, len(distinctions) + 1):
        for indices in combinations(range(len(distinctions)), degree):
            overlap = set(distinctions[indices[0]]["purview_union"])
            for index in indices[1:]:
                overlap &= set(distinctions[index]["purview_union"])
            if not overlap:
                continue
            phi = len(overlap) * min(
                distinctions[index]["phi"] / len(distinctions[index]["purview_union"])
                for index in indices
            )
            if phi > 1e-12:
                relations.append((indices, frozenset(overlap), phi))
    return relations


def structure(step, current):
    cause_states, effect_states, phi_s = system_state_specification(step, current)
    if not cause_states:
        return {
            "state": list(current),
            "phi_s": phi_s,
            "distinctions": [],
            "num_distinctions": 0,
            "num_relations": 0,
            "sum_phi_distinctions": 0.0,
            "sum_phi_relations": 0.0,
            "big_phi": 0.0,
        }

    choices = []
    for mechanism in nonempty_powerset(NODES):
        causes = [
            reading for reading in mice(step, current, "cause", mechanism)
            if reading["phi"] > 1e-12 and congruent(reading, cause_states)
        ]
        effects = [
            reading for reading in mice(step, current, "effect", mechanism)
            if reading["phi"] > 1e-12 and congruent(reading, effect_states)
        ]
        options = []
        for cause in causes:
            for effect in effects:
                phi = min(cause["phi"], effect["phi"])
                if phi > 1e-12:
                    options.append(
                        {
                            "mechanism": mechanism,
                            "phi": phi,
                            "cause": cause,
                            "effect": effect,
                        }
                    )
        if options:
            choices.append(options)

    candidate_structures = [[]]
    for options in choices:
        candidate_structures = [old + [option] for old in candidate_structures for option in options]

    best = None
    for distinctions in candidate_structures:
        distinctions = [dict(d) for d in distinctions]
        relations = relation_summary(distinctions)
        sum_d = sum(d["phi"] for d in distinctions)
        sum_r = sum(relation[2] for relation in relations)
        big_phi = sum_d + sum_r
        if best is None or (big_phi, sum_d) > best[0]:
            best = ((big_phi, sum_d), distinctions, relations)

    if best is None:
        distinctions, relations = [], []
    else:
        distinctions, relations = best[1], best[2]

    sum_d = sum(d["phi"] for d in distinctions)
    sum_r = sum(relation[2] for relation in relations)
    serialized = [
        {
            "mechanism": list(d["mechanism"]),
            "phi": d["phi"],
            "cause_purview": list(d["cause"]["purview"]),
            "cause_state": list(d["cause"]["state"]),
            "effect_purview": list(d["effect"]["purview"]),
            "effect_state": list(d["effect"]["state"]),
        }
        for d in distinctions
    ]
    return {
        "state": list(current),
        "system_cause_states": [list(s) for s in cause_states],
        "system_effect_states": [list(s) for s in effect_states],
        "phi_s": phi_s,
        "distinctions": serialized,
        "num_distinctions": len(distinctions),
        "num_relations": len(relations),
        "sum_phi_distinctions": sum_d,
        "sum_phi_relations": sum_r,
        "big_phi": sum_d + sum_r,
        "candidate_congruent_structures": len(candidate_structures),
    }


def validate_xor_golden():
    result = structure(xor_step, (0, 0, 0))
    expected = [
        ((0, 1), 0.5, (0, 1, 2), (2,)),
        ((0, 1, 2), 1.0, (0, 1, 2), (0, 1, 2)),
        ((0, 2), 0.5, (0, 1, 2), (1,)),
        ((1, 2), 0.5, (0, 1, 2), (0,)),
    ]
    actual = sorted(
        (
            tuple(d["mechanism"]),
            d["phi"],
            tuple(d["cause_purview"]),
            tuple(d["effect_purview"]),
        )
        for d in result["distinctions"]
    )
    assert result["phi_s"] == 1.5
    assert actual == sorted(expected)
    assert result["num_distinctions"] == 4
    assert result["num_relations"] == 15
    assert abs(result["sum_phi_relations"] - 7.0) < 1e-12
    assert abs(result["big_phi"] - GOLDEN_BIG_PHI) < 1e-12
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", choices=("xor", "triadic", "both"), default="both")
    parser.add_argument("--output")
    args = parser.parse_args()

    golden = validate_xor_golden()
    payload = {
        "authority": {
            "pyphi_repository": "https://github.com/wmayner/pyphi",
            "source_commit": SOURCE_COMMIT,
            "golden_fixture": "test/data/golden/v1/xor_iit4_2023.json",
            "golden_calibration_passed": True,
            "formalism": "IIT_4_0_2023",
            "boundary": "source-derived finite reference; PyPhi remains numerical authority",
        },
        "golden_xor_000": golden,
    }
    if args.model in ("xor", "both"):
        payload["xor"] = [structure(xor_step, state) for state in STATES]
    if args.model in ("triadic", "both"):
        payload["triadic"] = [structure(triadic_step, state) for state in STATES]

    text = json.dumps(payload, indent=2, sort_keys=True)
    if args.output:
        Path(args.output).write_text(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
