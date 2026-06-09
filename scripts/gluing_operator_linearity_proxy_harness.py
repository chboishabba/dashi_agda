#!/usr/bin/env python3
"""Finite proxy tests for gluing-operator linearity on a defect quotient.

This harness is diagnostic only.  It models a defect-section quotient by
splitting R^n into observable coordinates and null/gauge coordinates.  A
well-defined gluing operator must ignore null representatives and act linearly
on quotient classes.

The script compares:
  * a quotient-linear operator, which should pass;
  * a nonlinear representative-dependent counterexample, which should fail.

It emits JSON and always keeps promotion=false.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Any


Vector = list[float]
Matrix = list[list[float]]


def dot(row: Vector, vector: Vector) -> float:
    return sum(a * b for a, b in zip(row, vector))


def mat_vec(matrix: Matrix, vector: Vector) -> Vector:
    return [dot(row, vector) for row in matrix]


def add(x: Vector, y: Vector) -> Vector:
    return [a + b for a, b in zip(x, y)]


def sub(x: Vector, y: Vector) -> Vector:
    return [a - b for a, b in zip(x, y)]


def scale(alpha: float, x: Vector) -> Vector:
    return [alpha * value for value in x]


def norm2(x: Vector) -> float:
    return math.sqrt(sum(value * value for value in x))


def max_abs(x: Vector) -> float:
    return max((abs(value) for value in x), default=0.0)


def observable_projection(x: Vector, quotient_dim: int) -> Vector:
    return x[:quotient_dim]


def lift_observable(q: Vector, ambient_dim: int) -> Vector:
    return q + [0.0] * (ambient_dim - len(q))


def random_vector(rng: random.Random, dim: int, radius: float = 1.0) -> Vector:
    return [rng.uniform(-radius, radius) for _ in range(dim)]


def random_null_vector(rng: random.Random, ambient_dim: int, quotient_dim: int) -> Vector:
    return [0.0] * quotient_dim + [
        rng.uniform(-1.0, 1.0) for _ in range(ambient_dim - quotient_dim)
    ]


def deterministic_linear_matrix(dim: int) -> Matrix:
    """Stable nontrivial matrix with mixed signs and no random dependency."""
    matrix: Matrix = []
    for i in range(dim):
        row: Vector = []
        for j in range(dim):
            diagonal = 1.0 if i == j else 0.0
            skew = 0.11 * ((i + 1) - (j + 1))
            low_rank = 0.03 * ((i + 1) * (j + 2))
            row.append(diagonal + skew + low_rank)
        matrix.append(row)
    return matrix


@dataclass(frozen=True)
class OperatorCase:
    name: str
    description: str
    promotion: bool = False

    def apply(self, x: Vector, quotient_dim: int, matrix: Matrix) -> Vector:
        q = observable_projection(x, quotient_dim)
        if self.name == "quotient_linear":
            return mat_vec(matrix, q)
        if self.name == "nonlinear_representative_dependent":
            null_energy = sum(value * value for value in x[quotient_dim:])
            nonlinear = [value * value for value in q]
            base = mat_vec(matrix, q)
            if base:
                base[0] += 0.35 * null_energy
            return add(base, scale(0.25, nonlinear))
        raise ValueError(f"unknown operator case: {self.name}")


def representative_variant(
    rng: random.Random, x: Vector, ambient_dim: int, quotient_dim: int
) -> Vector:
    return add(x, random_null_vector(rng, ambient_dim, quotient_dim))


def run_case(
    rng: random.Random,
    case: OperatorCase,
    ambient_dim: int,
    quotient_dim: int,
    samples: int,
    tolerance: float,
) -> dict[str, Any]:
    matrix = deterministic_linear_matrix(quotient_dim)
    add_errors: list[float] = []
    scalar_errors: list[float] = []
    representative_errors: list[float] = []
    four_point_errors: list[float] = []
    worst_examples: list[dict[str, Any]] = []

    for index in range(samples):
        x = random_vector(rng, ambient_dim)
        y = random_vector(rng, ambient_dim)
        alpha = rng.uniform(-2.0, 2.0)
        gx = case.apply(x, quotient_dim, matrix)
        gy = case.apply(y, quotient_dim, matrix)
        g_add = case.apply(add(x, y), quotient_dim, matrix)
        add_error = norm2(sub(g_add, add(gx, gy)))
        add_errors.append(add_error)

        g_scalar = case.apply(scale(alpha, x), quotient_dim, matrix)
        scalar_error = norm2(sub(g_scalar, scale(alpha, gx)))
        scalar_errors.append(scalar_error)

        x_rep = representative_variant(rng, x, ambient_dim, quotient_dim)
        representative_error = norm2(sub(case.apply(x_rep, quotient_dim, matrix), gx))
        representative_errors.append(representative_error)

        # A quotient-linear gluing map should preserve the induced quadratic
        # parallelogram identity on the observable output norm.
        g_x_plus_y = case.apply(add(x, y), quotient_dim, matrix)
        g_x_minus_y = case.apply(sub(x, y), quotient_dim, matrix)
        four_point = (
            norm2(g_x_plus_y) ** 2
            + norm2(g_x_minus_y) ** 2
            - 2.0 * norm2(gx) ** 2
            - 2.0 * norm2(gy) ** 2
        )
        four_point_errors.append(abs(four_point))

        combined = max(add_error, scalar_error, representative_error, abs(four_point))
        if len(worst_examples) < 4 or combined > worst_examples[-1]["combined_error"]:
            worst_examples.append(
                {
                    "sample": index,
                    "alpha": alpha,
                    "additivity_error": add_error,
                    "scalar_error": scalar_error,
                    "representative_error": representative_error,
                    "four_point_error": abs(four_point),
                    "combined_error": combined,
                    "quotient_x": observable_projection(x, quotient_dim),
                    "quotient_y": observable_projection(y, quotient_dim),
                }
            )
            worst_examples.sort(key=lambda item: item["combined_error"], reverse=True)
            worst_examples = worst_examples[:4]

    max_add = max(add_errors, default=0.0)
    max_scalar = max(scalar_errors, default=0.0)
    max_representative = max(representative_errors, default=0.0)
    max_four_point = max(four_point_errors, default=0.0)
    passed = (
        max_add <= tolerance
        and max_scalar <= tolerance
        and max_representative <= tolerance
        and max_four_point <= tolerance
    )
    return {
        "name": case.name,
        "description": case.description,
        "promotion": case.promotion,
        "passed_all_proxy_checks": passed,
        "checks": {
            "additivity": max_add <= tolerance,
            "scalar_compatibility": max_scalar <= tolerance,
            "representative_compatibility": max_representative <= tolerance,
            "quadratic_four_point_output": max_four_point <= tolerance,
        },
        "max_errors": {
            "additivity": max_add,
            "scalar_compatibility": max_scalar,
            "representative_compatibility": max_representative,
            "quadratic_four_point_output": max_four_point,
            "combined": max(max_add, max_scalar, max_representative, max_four_point),
        },
        "mean_errors": {
            "additivity": sum(add_errors) / len(add_errors),
            "scalar_compatibility": sum(scalar_errors) / len(scalar_errors),
            "representative_compatibility": sum(representative_errors)
            / len(representative_errors),
            "quadratic_four_point_output": sum(four_point_errors) / len(four_point_errors),
        },
        "worst_examples": worst_examples,
    }


def build_summary(args: argparse.Namespace) -> dict[str, Any]:
    if args.ambient_dim <= 0:
        raise SystemExit("--ambient-dim must be positive")
    if args.quotient_dim <= 0:
        raise SystemExit("--quotient-dim must be positive")
    if args.quotient_dim >= args.ambient_dim:
        raise SystemExit("--quotient-dim must be smaller than --ambient-dim")
    if args.samples <= 0:
        raise SystemExit("--samples must be positive")
    if args.tolerance <= 0:
        raise SystemExit("--tolerance must be positive")

    rng = random.Random(args.seed)
    cases = [
        OperatorCase(
            name="quotient_linear",
            description=(
                "Applies a fixed matrix to observable quotient coordinates and ignores null representatives."
            ),
        ),
        OperatorCase(
            name="nonlinear_representative_dependent",
            description=(
                "Adds coordinate squares and null-energy dependence; expected to fail quotient-linearity."
            ),
        ),
    ]
    results = [
        run_case(
            rng=random.Random(rng.randrange(2**63)),
            case=case,
            ambient_dim=args.ambient_dim,
            quotient_dim=args.quotient_dim,
            samples=args.samples,
            tolerance=args.tolerance,
        )
        for case in cases
    ]
    linear = next(item for item in results if item["name"] == "quotient_linear")
    nonlinear = next(
        item for item in results if item["name"] == "nonlinear_representative_dependent"
    )
    ok = bool(
        linear["passed_all_proxy_checks"]
        and not nonlinear["passed_all_proxy_checks"]
        and nonlinear["max_errors"]["combined"] > args.counterexample_min_error
    )
    return {
        "control": {
            "O": "Lane 6 unification gluing diagnostic harness.",
            "R": "Test additivity, scalar compatibility, and representative compatibility for finite defect-section quotient proxies.",
            "C": "scripts/gluing_operator_linearity_proxy_harness.py",
            "S": "Pure finite proxy only; the admissible defect quotient theorem remains open.",
            "L": "construct quotient proxy -> test linear gluing -> test nonlinear counterexample -> emit fail-closed JSON",
            "P": "Use deterministic finite-dimensional operators with randomized samples.",
            "G": "promotion=false always; diagnostics cannot prove unification or Clay claims.",
            "F": "Does not define the real quotient V or prove GluingResidualForcesFourPointCancellation.",
        },
        "promotion": False,
        "clay_promotion": False,
        "unification_promotion": False,
        "ok": ok,
        "parameters": {
            "ambient_dim": args.ambient_dim,
            "quotient_dim": args.quotient_dim,
            "samples": args.samples,
            "seed": args.seed,
            "tolerance": args.tolerance,
            "counterexample_min_error": args.counterexample_min_error,
        },
        "summary": {
            "linear_case_passed": linear["passed_all_proxy_checks"],
            "nonlinear_counterexample_failed": not nonlinear["passed_all_proxy_checks"],
            "nonlinear_counterexample_visible": nonlinear["max_errors"]["combined"]
            > args.counterexample_min_error,
            "all_expected_outcomes_observed": ok,
        },
        "cases": results,
        "interpretation": {
            "supports": (
                "Linearity plus representative independence is checkable on finite quotient proxies."
            ),
            "rejects": (
                "Nonlinear or representative-dependent gluing operators can satisfy neither quotient compatibility nor four-point cancellation in this proxy."
            ),
            "residual_gap": (
                "The repo still needs the actual admissible defect quotient V and a proof that the true gluing operator acts linearly on it."
            ),
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ambient-dim", type=int, default=6)
    parser.add_argument("--quotient-dim", type=int, default=4)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--seed", type=int, default=20260608)
    parser.add_argument("--tolerance", type=float, default=1e-10)
    parser.add_argument("--counterexample-min-error", type=float, default=1e-3)
    parser.add_argument("--json-output", type=Path)
    parser.add_argument("--json", action="store_true", help="print JSON summary")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    summary = build_summary(args)
    if args.json_output is not None:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("gluing operator linearity proxy harness")
        print(f"ok={str(summary['ok']).lower()}")
        print("promotion=false")
        for item in summary["cases"]:
            print(
                f"{item['name']}: passed={str(item['passed_all_proxy_checks']).lower()} "
                f"combined_error={item['max_errors']['combined']:.6g}"
            )
    return 0 if summary["ok"] and not summary["promotion"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
