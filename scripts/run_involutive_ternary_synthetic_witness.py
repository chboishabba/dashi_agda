#!/usr/bin/env python3
"""Deterministic synthetic witness for the involutive ternary proof programme.

This script is intentionally diagnostic-only.  It compares four nested
representations on a known ternary process:

1. ordinary signed residuals against a zero predictor;
2. involution quotienting (support plus sign-on-support);
3. three-to-one saturating coarse blocks;
4. an MDL gate choosing zero or persistence prediction per regime.

It reports active residual densities, side cost, residual cost, exact prediction
error, and a small operation-count proxy.  It does not claim general compression,
learning, financial, or physical performance.
"""

from __future__ import annotations

import argparse
import csv
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

Trit = int


def inv(x: Trit) -> Trit:
    return -x


def sat_add(x: Trit, y: Trit) -> Trit:
    return max(-1, min(1, x + y))


def coarse3(xs: Sequence[Trit]) -> list[Trit]:
    if len(xs) % 3:
        raise ValueError("sequence length must be divisible by 3")
    return [sat_add(sat_add(xs[i], xs[i + 1]), xs[i + 2]) for i in range(0, len(xs), 3)]


def synthetic_process(length: int) -> list[Trit]:
    """Known piecewise process with symmetric regimes and sparse shocks."""
    if length < 12 or length % 3:
        raise ValueError("length must be a multiple of 3 and at least 12")
    out: list[Trit] = []
    for t in range(length):
        regime = (t // 24) % 4
        base = (0, 1, 0, -1)[regime]
        shock = 0
        if t % 17 == 0:
            shock = -base if base else (1 if (t // 17) % 2 == 0 else -1)
        if t % 29 == 0:
            shock = inv(base)
        out.append(sat_add(base, shock))
    return out


def residuals(xs: Sequence[Trit], predictor: Sequence[Trit]) -> list[int]:
    return [x - p for x, p in zip(xs, predictor, strict=True)]


def active_density(rs: Iterable[int], threshold: int) -> float:
    values = list(rs)
    return sum(abs(r) > threshold for r in values) / len(values)


def signed_symbol_cost(rs: Sequence[int]) -> int:
    # Fixed diagnostic code: 2 bits for each value in {-2,-1,0,1,2} after
    # separating an escape for magnitude two.  It is intentionally simple.
    return sum(2 if abs(r) <= 1 else 3 for r in rs)


def quotient_cost(rs: Sequence[int]) -> int:
    support = sum(r != 0 for r in rs)
    magnitude_two = sum(abs(r) == 2 for r in rs)
    return len(rs) + support + magnitude_two


def persistence_predictor(xs: Sequence[Trit]) -> list[Trit]:
    return [0, *xs[:-1]]


def mdl_regime_predictor(xs: Sequence[Trit], block: int = 24) -> tuple[list[Trit], int]:
    """Choose zero or persistence per block using explicit side+residual cost."""
    pred: list[Trit] = []
    side_bits = 0
    for start in range(0, len(xs), block):
        chunk = list(xs[start : start + block])
        zero = [0] * len(chunk)
        previous_seed = xs[start - 1] if start else 0
        persist = [previous_seed, *chunk[:-1]]
        zero_cost = quotient_cost(residuals(chunk, zero))
        persist_cost = quotient_cost(residuals(chunk, persist))
        side_bits += 1
        pred.extend(persist if persist_cost < zero_cost else zero)
    return pred, side_bits


@dataclass(frozen=True)
class Result:
    model: str
    samples: int
    rho0: float
    rho1: float
    side_bits: int
    residual_bits: int
    total_bits: int
    absolute_error: int
    operation_proxy: int


def evaluate(name: str, xs: Sequence[Trit], pred: Sequence[Trit], side: int, ops: int) -> Result:
    rs = residuals(xs, pred)
    residual_bits = quotient_cost(rs) if name != "ordinary" else signed_symbol_cost(rs)
    return Result(
        model=name,
        samples=len(xs),
        rho0=active_density(rs, 0),
        rho1=active_density(rs, 1),
        side_bits=side,
        residual_bits=residual_bits,
        total_bits=side + residual_bits,
        absolute_error=sum(abs(r) for r in rs),
        operation_proxy=ops,
    )


def run(length: int) -> list[Result]:
    xs = synthetic_process(length)
    zero = [0] * length
    persist = persistence_predictor(xs)
    mdl_pred, mdl_side = mdl_regime_predictor(xs)

    coarse_x = coarse3(xs)
    coarse_zero = [0] * len(coarse_x)

    return [
        evaluate("ordinary", xs, zero, 0, length),
        evaluate("involution-quotient", xs, zero, 0, 2 * length),
        evaluate("multiscale-coarse3", coarse_x, coarse_zero, 0, length + len(coarse_x)),
        evaluate("mdl-zero-or-persistence", xs, mdl_pred, mdl_side, 3 * length),
        # Persistence is retained as an internal comparator in the JSON notes,
        # but the requested four-model ladder remains the headline output.
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--length", type=int, default=288)
    parser.add_argument("--out", type=Path, default=Path("artifacts/involutive_ternary_witness"))
    args = parser.parse_args()

    results = run(args.length)
    args.out.mkdir(parents=True, exist_ok=True)

    json_path = args.out / "summary.json"
    csv_path = args.out / "summary.csv"
    json_path.write_text(
        json.dumps(
            {
                "status": "diagnostic-only",
                "claim_boundary": (
                    "Synthetic representation comparison; no general physical, "
                    "economic, learning, or compression superiority claim."
                ),
                "results": [asdict(r) for r in results],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(asdict(results[0]).keys()))
        writer.writeheader()
        writer.writerows(asdict(r) for r in results)

    print(json.dumps([asdict(r) for r in results], indent=2))
    print(f"wrote {json_path}")
    print(f"wrote {csv_path}")


if __name__ == "__main__":
    main()
