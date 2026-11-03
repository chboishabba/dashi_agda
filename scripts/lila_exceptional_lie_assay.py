#!/usr/bin/env python3
"""Infinitesimal exceptional-Lie assay for LILA/teleodynamic trajectories.

DASHI empirical tooling; never theorem or mechanism authority.

This complements `lila_exceptional_weyl_assay.py`.  The finite assay asks
whether predeclared discrete generators and held-out Weyl/Tits words act as
predicted.  This assay asks the stronger Lie-level questions exposed by the
native Albert/F4 Cartan and split-root programme:

* derivative/generator residuals on held-out states;
* commutator/bracket residuals;
* root/weight eigen-relation residuals;
* held-out finite-flow residuals.

All candidate matrices, brackets, weights and flow maps are supplied
independently of the measured samples.  The script does not infer an F4/E6/E8
ontology from a low residual and never promotes fit to mechanism,
phenomenology, or scientific authority.

Usage:
    python3 scripts/lila_exceptional_lie_assay.py --self-test
    python3 scripts/lila_exceptional_lie_assay.py receipt.json
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
    if len(a[0]) != len(b):
        raise ValueError("matrix shape mismatch")
    if any(len(r) != len(a[0]) for r in a) or any(len(r) != len(b[0]) for r in b):
        raise ValueError("ragged matrix")
    return [
        [sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))]
        for i in range(len(a))
    ]


def matsub(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    if len(a) != len(b) or any(len(x) != len(y) for x, y in zip(a, b)):
        raise ValueError("matrix shape mismatch")
    return [[x - y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def matvec(a: list[list[float]], x: list[float]) -> list[float]:
    if any(len(row) != len(x) for row in a):
        raise ValueError("matrix/vector shape mismatch")
    return [sum(v * w for v, w in zip(row, x)) for row in a]


def scalevec(c: float, x: list[float]) -> list[float]:
    return [c * a for a in x]


def vnorm(x: list[float]) -> float:
    return math.sqrt(sum(float(a) * float(a) for a in x))


def fnorm(a: list[list[float]]) -> float:
    return math.sqrt(sum(float(x) * float(x) for row in a for x in row))


def vrel(a: list[float], b: list[float], eps: float = 1e-12) -> float:
    if len(a) != len(b):
        raise ValueError("vector shape mismatch")
    d = [x - y for x, y in zip(a, b)]
    return vnorm(d) / max(vnorm(a), vnorm(b), eps)


def mrel(a: list[list[float]], b: list[list[float]], eps: float = 1e-12) -> float:
    return fnorm(matsub(a, b)) / max(fnorm(a), fnorm(b), eps)


def commutator(a: list[list[float]], b: list[list[float]]) -> list[list[float]]:
    return matsub(matmul(a, b), matmul(b, a))


def rms(xs: list[float]) -> float | None:
    if not xs:
        return None
    return math.sqrt(sum(x * x for x in xs) / len(xs))


def grade(value: float | None, threshold: float, present: bool) -> str:
    if not present or value is None:
        return "unresolved"
    return "verified" if value <= threshold else "refuted"


def assess(doc: dict[str, Any]) -> dict[str, Any]:
    generators: dict[str, list[list[float]]] = doc["lie_generators"]
    thresholds = {
        "derivative": 1e-8,
        "commutator": 1e-8,
        "root_weight": 1e-8,
        "flow": 1e-8,
    }
    thresholds.update(doc.get("thresholds", {}))

    derivative_residuals: list[float] = []
    covered: set[str] = set()
    for s in doc.get("derivative_samples", []):
        g = s["generator"]
        covered.add(g)
        derivative_residuals.append(vrel(s["dz"], matvec(generators[g], s["z"])))
    derivative_rms = rms(derivative_residuals)
    complete_generators = bool(generators) and covered == set(generators)

    commutator_residuals: list[float] = []
    for r in doc.get("commutator_relations", []):
        actual = commutator(generators[r["left"]], generators[r["right"]])
        expected = r["expected_matrix"]
        commutator_residuals.append(mrel(actual, expected))
    commutator_rms = rms(commutator_residuals)

    root_weight_residuals: list[float] = []
    for s in doc.get("root_weight_samples", []):
        actual = matvec(generators[s["generator"]], s["vector"])
        expected = scalevec(float(s["weight"]), s["vector"])
        root_weight_residuals.append(vrel(actual, expected))
    root_weight_rms = rms(root_weight_residuals)

    flow_residuals: list[float] = []
    for s in doc.get("heldout_flow_samples", []):
        actual = matvec(s["expected_flow_matrix"], s["z"])
        flow_residuals.append(vrel(s["z_after"], actual))
    flow_rms = rms(flow_residuals)

    checks = {
        "derivative": {
            "rms": derivative_rms,
            "complete_generators": complete_generators,
            "status": grade(
                derivative_rms,
                thresholds["derivative"],
                complete_generators and bool(derivative_residuals),
            ),
        },
        "commutator": {
            "rms": commutator_rms,
            "status": grade(
                commutator_rms, thresholds["commutator"], bool(commutator_residuals)
            ),
        },
        "root_weight": {
            "rms": root_weight_rms,
            "status": grade(
                root_weight_rms, thresholds["root_weight"], bool(root_weight_residuals)
            ),
        },
        "heldout_flow": {
            "rms": flow_rms,
            "status": grade(flow_rms, thresholds["flow"], bool(flow_residuals)),
        },
    }

    required = ["derivative", "commutator", "root_weight", "heldout_flow"]
    if any(checks[k]["status"] == "refuted" for k in required):
        overall = "refuted"
    elif all(checks[k]["status"] == "verified" for k in required):
        overall = "verified"
    else:
        overall = "unresolved"

    return {
        "candidate": doc.get("candidate", "unspecified"),
        "checks": checks,
        "overall": overall,
        "rational_form_identity": False,
        "algebraic_group_identity": False,
        "mechanism_identity": False,
        "phenomenal_identity": False,
        "scientific_authority": False,
    }


def self_test() -> None:
    # Two commuting diagonal Cartan-like generators.  This tests only the assay
    # engine, not an exceptional-group claim.
    h0 = [[1.0, 0.0], [0.0, -1.0]]
    h1 = [[2.0, 0.0], [0.0, 3.0]]
    z = [0.4, -0.7]
    zero = [[0.0, 0.0], [0.0, 0.0]]
    t = 0.35
    flow0 = [[math.exp(t), 0.0], [0.0, math.exp(-t)]]

    doc: dict[str, Any] = {
        "candidate": "commuting-Cartan-smoke-fixture",
        "lie_generators": {"h0": h0, "h1": h1},
        "derivative_samples": [
            {"generator": "h0", "z": z, "dz": matvec(h0, z)},
            {"generator": "h1", "z": z, "dz": matvec(h1, z)},
        ],
        "commutator_relations": [
            {"left": "h0", "right": "h1", "expected_matrix": zero}
        ],
        "root_weight_samples": [
            {"generator": "h0", "vector": [1.0, 0.0], "weight": 1.0},
            {"generator": "h1", "vector": [0.0, 1.0], "weight": 3.0},
        ],
        "heldout_flow_samples": [
            {
                "expected_flow_matrix": flow0,
                "z": [0.2, 0.8],
                "z_after": matvec(flow0, [0.2, 0.8]),
            }
        ],
    }

    good = assess(doc)
    assert good["overall"] == "verified", good
    assert not good["rational_form_identity"]
    assert not good["algebraic_group_identity"]
    assert not good["mechanism_identity"]
    assert not good["phenomenal_identity"]

    broken = copy.deepcopy(doc)
    broken["derivative_samples"][1]["dz"][0] += 0.25
    bad = assess(broken)
    assert bad["overall"] == "refuted", bad
    assert bad["checks"]["derivative"]["status"] == "refuted", bad

    print("exact infinitesimal fixture : verified")
    print("broken derivative fixture   : refuted")
    print("group/mechanism identity    : never auto-promoted")
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
    doc = json.loads(args.receipt.read_text())
    print(json.dumps(assess(doc), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
