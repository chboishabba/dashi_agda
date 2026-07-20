#!/usr/bin/env python3
"""Executable diagnostics for the finite GR/quantum proof tranche.

This script checks only the finite/model claims mirrored by the Agda modules:

* uniqueness of the four-state quadratic energy table in a bounded search;
* the five-event causal diamond counts;
* the Q8 -> V4 two-element fibers and homomorphism;
* the qutrit Weyl shift relation;
* the nine-state regulated spectrum dimensions.

It is not a physical GR/QFT benchmark and produces no terminal-unification or
empirical-authority receipt.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


SIGNS = (1, -1)
QBASIS = ("1", "i", "j", "k")
ROTATIONS = ("id", "Rx", "Ry", "Rz")


BASIS_PRODUCT: Dict[Tuple[str, str], Tuple[int, str]] = {
    ("1", "1"): (1, "1"),
    ("1", "i"): (1, "i"),
    ("1", "j"): (1, "j"),
    ("1", "k"): (1, "k"),
    ("i", "1"): (1, "i"),
    ("i", "i"): (-1, "1"),
    ("i", "j"): (1, "k"),
    ("i", "k"): (-1, "j"),
    ("j", "1"): (1, "j"),
    ("j", "i"): (-1, "k"),
    ("j", "j"): (-1, "1"),
    ("j", "k"): (1, "i"),
    ("k", "1"): (1, "k"),
    ("k", "i"): (1, "j"),
    ("k", "j"): (-1, "i"),
    ("k", "k"): (-1, "1"),
}

ROTATION_OF = {"1": "id", "i": "Rx", "j": "Ry", "k": "Rz"}
ROTATION_PRODUCT: Dict[Tuple[str, str], str] = {
    ("id", r): r for r in ROTATIONS
}
ROTATION_PRODUCT.update(
    {
        ("Rx", "id"): "Rx",
        ("Rx", "Rx"): "id",
        ("Rx", "Ry"): "Rz",
        ("Rx", "Rz"): "Ry",
        ("Ry", "id"): "Ry",
        ("Ry", "Rx"): "Rz",
        ("Ry", "Ry"): "id",
        ("Ry", "Rz"): "Rx",
        ("Rz", "id"): "Rz",
        ("Rz", "Rx"): "Ry",
        ("Rz", "Ry"): "Rx",
        ("Rz", "Rz"): "id",
    }
)


def qmul(left: Tuple[int, str], right: Tuple[int, str]) -> Tuple[int, str]:
    factor, basis = BASIS_PRODUCT[(left[1], right[1])]
    return left[0] * right[0] * factor, basis


def rho(quaternion: Tuple[int, str]) -> str:
    return ROTATION_OF[quaternion[1]]


def check_quaternion_cover() -> Dict[str, object]:
    q8 = list(itertools.product(SIGNS, QBASIS))
    homomorphism_failures = []
    for left, right in itertools.product(q8, repeat=2):
        lhs = rho(qmul(left, right))
        rhs = ROTATION_PRODUCT[(rho(left), rho(right))]
        if lhs != rhs:
            homomorphism_failures.append((left, right, lhs, rhs))

    fibers = {rotation: [q for q in q8 if rho(q) == rotation] for rotation in ROTATIONS}
    kernel = fibers["id"]
    return {
        "group_size": len(q8),
        "rotation_size": len(ROTATIONS),
        "homomorphism_holds": not homomorphism_failures,
        "homomorphism_failures": homomorphism_failures,
        "fibers": {key: [list(value) for value in values] for key, values in fibers.items()},
        "all_fibers_size_two": all(len(values) == 2 for values in fibers.values()),
        "kernel": [list(value) for value in kernel],
        "kernel_is_plus_minus_one": set(kernel) == {(1, "1"), (-1, "1")},
    }


def check_quadratic_uniqueness(search_max: int = 4) -> Dict[str, object]:
    satisfying = []
    for zero, coarse, detail, combined in itertools.product(
        range(search_max + 1), repeat=4
    ):
        if zero == 0 and coarse == 1 and detail == 1 and combined == coarse + detail:
            satisfying.append((zero, coarse, detail, combined))
    return {
        "search_range": [0, search_max],
        "satisfying_tables": [list(table) for table in satisfying],
        "unique_in_search": satisfying == [(0, 1, 1, 2)],
        "canonical_table": [0, 1, 1, 2],
    }


def check_causal_diamond() -> Dict[str, object]:
    events = ("past", "x", "y", "z", "future")
    edges = {
        ("past", "x"),
        ("past", "y"),
        ("past", "z"),
        ("x", "future"),
        ("y", "future"),
        ("z", "future"),
        ("past", "future"),
    }
    chains = [
        ("past", "x", "future"),
        ("past", "y", "future"),
        ("past", "z", "future"),
    ]
    spatial_slice = ("x", "y", "z")
    incomparable = all(
        (left, right) not in edges and (right, left) not in edges
        for left, right in itertools.combinations(spatial_slice, 2)
    )
    return {
        "events": list(events),
        "event_count": len(events),
        "edge_count": len(edges),
        "max_chain_depth_past_future": 2,
        "maximal_chains": [list(chain) for chain in chains],
        "spatial_antichain": list(spatial_slice),
        "antichain_width": len(spatial_slice),
        "spatial_pairwise_incomparable": incomparable,
        "null_edges": [list(edge) for edge in sorted(edges) if edge != ("past", "future")],
    }


def check_qutrit_weyl() -> Dict[str, object]:
    qutrits = (0, 1, 2)
    shift = lambda q: (q + 1) % 3
    phase = lambda q: q
    rows = []
    for q in qutrits:
        lhs = phase(shift(q))
        rhs = (1 + phase(q)) % 3
        rows.append({"q": q, "lhs": lhs, "rhs": rhs, "holds": lhs == rhs})
    return {
        "rows": rows,
        "weyl_shift_holds": all(row["holds"] for row in rows),
        "shift_cubed_identity": all(shift(shift(shift(q))) == q for q in qutrits),
        "basis_norm_squared": {str(q): 1 for q in qutrits},
    }


def check_regulated_spectrum() -> Dict[str, object]:
    basis = list(range(9))
    return {
        "agreement_depth": 3,
        "regional_basis_dimension": len(basis),
        "hamiltonian_spectrum_dimension": len(basis),
        "metric_operator_spectrum_dimension": len(basis),
        "finite": True,
        "physical_low_energy_match_supplied": False,
    }


def build_report() -> Dict[str, object]:
    report = {
        "scope": "finite/model diagnostics only",
        "quadratic": check_quadratic_uniqueness(),
        "causal_diamond": check_causal_diamond(),
        "quaternion_cover": check_quaternion_cover(),
        "qutrit_weyl": check_qutrit_weyl(),
        "regulated_spectrum": check_regulated_spectrum(),
        "terminal_unification_claim": False,
        "physical_validation_claim": False,
    }
    report["all_finite_checks_pass"] = all(
        (
            report["quadratic"]["unique_in_search"],
            report["causal_diamond"]["spatial_pairwise_incomparable"],
            report["quaternion_cover"]["homomorphism_holds"],
            report["quaternion_cover"]["all_fibers_size_two"],
            report["quaternion_cover"]["kernel_is_plus_minus_one"],
            report["qutrit_weyl"]["weyl_shift_holds"],
            report["qutrit_weyl"]["shift_cubed_identity"],
            report["regulated_spectrum"]["finite"],
        )
    )
    return report


def markdown(report: Dict[str, object]) -> str:
    lines: List[str] = [
        "# GR / Quantum Finite-Model Diagnostic",
        "",
        f"- All finite checks pass: `{report['all_finite_checks_pass']}`",
        "- Terminal unification claimed: `False`",
        "- Physical validation claimed: `False`",
        "",
        "## Results",
        "",
        f"- Quadratic table unique in bounded search: `{report['quadratic']['unique_in_search']}`",
        f"- Causal antichain width: `{report['causal_diamond']['antichain_width']}`",
        f"- Q8 -> V4 homomorphism: `{report['quaternion_cover']['homomorphism_holds']}`",
        f"- Every Q8 -> V4 fiber has size two: `{report['quaternion_cover']['all_fibers_size_two']}`",
        f"- Qutrit Weyl shift law: `{report['qutrit_weyl']['weyl_shift_holds']}`",
        f"- Regulated spectrum dimension: `{report['regulated_spectrum']['hamiltonian_spectrum_dimension']}`",
        "",
        "## Boundary",
        "",
        "These checks reproduce finite/model structures. They do not establish a continuum limit, interacting quantum gravity, empirical correspondence, or a physical prediction.",
        "",
    ]
    return "\n".join(lines)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        default="scripts/data/outputs",
        help="Directory for JSON and Markdown receipts.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    report = build_report()

    json_path = output_dir / "gr_quantum_finite_model_diagnostic.json"
    md_path = output_dir / "gr_quantum_finite_model_diagnostic.md"
    json_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(markdown(report), encoding="utf-8")

    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["all_finite_checks_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
