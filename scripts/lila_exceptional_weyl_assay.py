#!/usr/bin/env python3
"""Empirical exceptional-Weyl/Tits action assay for LILA/teleodynamics.

DASHI experimental tooling, not theorem authority.

Input is a JSON document containing a predeclared candidate-coordinate action,
paired generator trajectories, exact/expected Coxeter or Tits relations, held-
out word trajectories, optional decoder compatibility samples, and optional
future-consumer samples.  The script does not fit the exceptional action from
the same held-out data: candidate generator matrices are supplied independently.

Evidence grades stay separate:
  root/codebook use
  < generator fit
  < Coxeter/Tits relation fit
  < held-out word fit
  < decoder compatibility
  < future-consumer fit.

Even complete verification never emits mechanism/phenomenology/authority=true.

Run a dependency-free synthetic smoke test with:

    python3 scripts/lila_exceptional_weyl_assay.py --self-test

Or assess a JSON receipt:

    python3 scripts/lila_exceptional_weyl_assay.py receipt.json
"""

from __future__ import annotations

import argparse
import copy
import json
import math
from pathlib import Path
from typing import Any


def matmul(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    if not a or not b:
        raise ValueError("empty matrix")
    p = len(b)
    if any(len(row) != p for row in a):
        raise ValueError("matrix shape mismatch")
    m = len(b[0])
    if any(len(row) != m for row in b):
        raise ValueError("ragged matrix")
    return [
        [sum(a[i][k] * b[k][j] for k in range(p)) for j in range(m)]
        for i in range(len(a))
    ]


def matvec(a: list[list[float]], x: list[float]) -> list[float]:
    if any(len(row) != len(x) for row in a):
        raise ValueError("matrix/vector shape mismatch")
    return [sum(v * w for v, w in zip(row, x)) for row in a]


def eye(n: int) -> list[list[float]]:
    return [[1.0 if i == j else 0.0 for j in range(n)] for i in range(n)]


def vector_norm(x: list[float]) -> float:
    return math.sqrt(sum(float(a) * float(a) for a in x))


def vector_relative_residual(a: list[float], b: list[float], eps: float = 1e-12) -> float:
    if len(a) != len(b):
        raise ValueError("vector shape mismatch")
    delta = [x - y for x, y in zip(a, b)]
    return vector_norm(delta) / max(vector_norm(a), vector_norm(b), eps)


def frobenius_norm(a: list[list[float]]) -> float:
    return math.sqrt(sum(float(x) * float(x) for row in a for x in row))


def matrix_relative_residual(
    a: list[list[float]], b: list[list[float]], eps: float = 1e-12
) -> float:
    if len(a) != len(b) or any(len(x) != len(y) for x, y in zip(a, b)):
        raise ValueError("matrix shape mismatch")
    delta = [[x - y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]
    return frobenius_norm(delta) / max(frobenius_norm(a), frobenius_norm(b), eps)


def word_matrix(generators: dict[str, list[list[float]]], word: list[str]) -> list[list[float]]:
    if not generators:
        raise ValueError("at least one generator is required")
    n = len(next(iter(generators.values())))
    out = eye(n)
    # Word order is application order: [g,h] means first g, then h, so the
    # resulting column-vector action is H*G.
    for name in word:
        if name not in generators:
            raise KeyError(f"unknown generator {name!r}")
        out = matmul(generators[name], out)
    return out


def rms(values: list[float]) -> float | None:
    if not values:
        return None
    return math.sqrt(sum(v * v for v in values) / len(values))


def status(value: float | None, threshold: float, present: bool) -> str:
    if not present or value is None:
        return "unresolved"
    return "verified" if value <= threshold else "refuted"


def assess(document: dict[str, Any]) -> dict[str, Any]:
    generators = document["generators"]
    thresholds = {
        "generator": 1e-8,
        "relation": 1e-8,
        "heldout_word": 1e-8,
        "decoder": 1e-8,
        "future_consumer": 1e-8,
    }
    thresholds.update(document.get("thresholds", {}))

    generator_residuals: list[float] = []
    covered_generators: set[str] = set()
    for sample in document.get("generator_samples", []):
        name = sample["generator"]
        covered_generators.add(name)
        predicted = matvec(generators[name], sample["z"])
        generator_residuals.append(vector_relative_residual(sample["z_prime"], predicted))
    generator_rms = rms(generator_residuals)
    all_generators_covered = bool(generators) and covered_generators == set(generators)

    relation_residuals: list[float] = []
    for relation in document.get("relations", []):
        left = word_matrix(generators, relation.get("left", []))
        right = word_matrix(generators, relation.get("right", []))
        relation_residuals.append(matrix_relative_residual(left, right))
    relation_rms = rms(relation_residuals)

    heldout_residuals: list[float] = []
    for sample in document.get("heldout_word_samples", []):
        action = word_matrix(generators, sample["word"])
        predicted = matvec(action, sample["z"])
        heldout_residuals.append(vector_relative_residual(sample["z_prime"], predicted))
    heldout_rms = rms(heldout_residuals)

    decoder_residuals: list[float] = []
    decoder = document.get("decoder")
    if decoder:
        decode = decoder["matrix"]
        output_actions = decoder["output_actions"]
        for sample in decoder.get("samples", []):
            name = sample["generator"]
            z = sample["z"]
            lhs = matvec(decode, matvec(generators[name], z))
            rhs = matvec(output_actions[name], matvec(decode, z))
            decoder_residuals.append(vector_relative_residual(lhs, rhs))
    decoder_rms = rms(decoder_residuals)

    future_residuals: list[float] = []
    for sample in document.get("future_consumer_samples", []):
        action = word_matrix(generators, sample["word"])
        predicted = matvec(sample["consumer_map"], matvec(action, sample["z"]))
        future_residuals.append(
            vector_relative_residual(sample["consumer_after"], predicted)
        )
    future_rms = rms(future_residuals)

    checks = {
        "generator": {
            "rms": generator_rms,
            "status": status(
                generator_rms,
                thresholds["generator"],
                all_generators_covered and bool(generator_residuals),
            ),
            "complete_generators": all_generators_covered,
        },
        "relations": {
            "rms": relation_rms,
            "status": status(relation_rms, thresholds["relation"], bool(relation_residuals)),
        },
        "heldout_words": {
            "rms": heldout_rms,
            "status": status(heldout_rms, thresholds["heldout_word"], bool(heldout_residuals)),
        },
        "decoder": {
            "rms": decoder_rms,
            "status": status(decoder_rms, thresholds["decoder"], bool(decoder_residuals)),
        },
        "future_consumer": {
            "rms": future_rms,
            "status": status(
                future_rms, thresholds["future_consumer"], bool(future_residuals)
            ),
        },
    }

    required = ["generator", "relations", "heldout_words", "decoder", "future_consumer"]
    if any(checks[name]["status"] == "refuted" for name in required):
        overall = "refuted"
    elif all(checks[name]["status"] == "verified" for name in required):
        overall = "verified"
    else:
        overall = "unresolved"

    return {
        "candidate": document.get("candidate", "unspecified"),
        "action_grade": document.get("action_grade", "unspecified"),
        "checks": checks,
        "overall": overall,
        # Authority firewall: mathematical/empirical action fit does not create
        # these stronger interpretations.
        "mechanism_identity": False,
        "phenomenal_identity": False,
        "scientific_authority": False,
    }


def reflection(theta: float) -> list[list[float]]:
    c = math.cos(2.0 * theta)
    s = math.sin(2.0 * theta)
    return [[c, s], [s, -c]]


def self_test() -> None:
    # Rank-2 Coxeter A2 smoke fixture. This is only a test of the assay engine;
    # it is not an exceptional-group scientific result.
    generators = {"s0": reflection(0.0), "s1": reflection(math.pi / 3.0)}
    identity = eye(2)
    z = [0.3, -1.2]
    document: dict[str, Any] = {
        "candidate": "A2-assay-smoke-fixture",
        "action_grade": "label-permutation-smoke",
        "generators": generators,
        "generator_samples": [
            {"generator": name, "z": z, "z_prime": matvec(action, z)}
            for name, action in generators.items()
        ],
        "relations": [
            {"name": "s0^2", "left": ["s0", "s0"], "right": []},
            {"name": "s1^2", "left": ["s1", "s1"], "right": []},
            {
                "name": "braid",
                "left": ["s0", "s1", "s0"],
                "right": ["s1", "s0", "s1"],
            },
        ],
        "heldout_word_samples": [
            {
                "word": ["s0", "s1"],
                "z": [0.7, 0.2],
                "z_prime": matvec(word_matrix(generators, ["s0", "s1"]), [0.7, 0.2]),
            }
        ],
        "decoder": {
            "matrix": identity,
            "output_actions": generators,
            "samples": [
                {"generator": "s0", "z": [0.4, 0.9]},
                {"generator": "s1", "z": [0.4, 0.9]},
            ],
        },
        "future_consumer_samples": [
            {
                "word": ["s1", "s0"],
                "z": [0.2, 0.5],
                "consumer_map": identity,
                "consumer_after": matvec(
                    word_matrix(generators, ["s1", "s0"]), [0.2, 0.5]
                ),
            }
        ],
    }

    good = assess(document)
    assert good["overall"] == "verified", good
    assert not good["mechanism_identity"]
    assert not good["phenomenal_identity"]
    assert not good["scientific_authority"]

    broken = copy.deepcopy(document)
    broken["heldout_word_samples"][0]["z_prime"][0] += 0.2
    bad = assess(broken)
    assert bad["overall"] == "refuted", bad
    assert bad["checks"]["heldout_words"]["status"] == "refuted", bad

    print("exact synthetic action fixture : verified")
    print("broken held-out word fixture  : refuted")
    print("mechanism/phenomenology       : never auto-promoted")
    print("RUN_TERMINAL COMPLETE")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("receipt", nargs="?", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        self_test()
        return
    if args.receipt is None:
        parser.error("provide a JSON receipt or --self-test")
    document = json.loads(args.receipt.read_text())
    print(json.dumps(assess(document), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
