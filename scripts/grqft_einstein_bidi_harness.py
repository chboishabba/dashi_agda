#!/usr/bin/env python3
"""Exact integer GR/QFT BIDI fixture for the finite warped Einstein/source model.

This script is diagnostic execution, not theorem authority.  It uses the same
normalized diagonal tensor pattern proved in
DASHI/Physics/Closure/DiscreteWarpedEinsteinMatterModel.agda and evaluates

    R_mu_nu(kappa) = G_mu_nu - kappa T_mu_nu

for an exact integer sweep.  kappa=1 is the dimensionless normalized coupling;
it is not an SI evaluation of 8*pi*G.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


G = (
    (1, 0, 0, 0),
    (0, -1, 0, 0),
    (0, 0, -1, 0),
    (0, 0, 0, -1),
)
T = G


def residual(kappa: int) -> list[list[int]]:
    return [
        [G[i][j] - kappa * T[i][j] for j in range(4)]
        for i in range(4)
    ]


def metrics(matrix: list[list[int]]) -> dict[str, int | bool]:
    absolute = [abs(x) for row in matrix for x in row]
    return {
        "l1": sum(absolute),
        "max_abs": max(absolute),
        "all_zero": all(x == 0 for x in absolute),
    }


def run(lo: int = -3, hi: int = 3) -> dict[str, object]:
    runs = []
    for kappa in range(lo, hi + 1):
        matrix = residual(kappa)
        runs.append(
            {
                "kappa_normalized": kappa,
                "residual": matrix,
                **metrics(matrix),
            }
        )

    zeros = [x["kappa_normalized"] for x in runs if x["all_zero"]]
    payload = {
        "model": "DASHI finite warped Einstein-matter normalized BIDI fixture",
        "equation": "G_mu_nu - kappa*T_mu_nu",
        "normalization": (
            "kappa=1 represents normalized 8*pi*G; this is not SI calibration"
        ),
        "runs": runs,
        "unique_zero_residual_kappa": zeros,
    }
    if zeros != [1]:
        raise AssertionError(
            f"expected unique normalized zero at kappa=1, got {zeros}"
        )
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("outputs/grqft_einstein_bidi_residual.json"),
    )
    args = parser.parse_args()
    payload = run()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
