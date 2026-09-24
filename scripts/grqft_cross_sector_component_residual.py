#!/usr/bin/env python3
"""Execute the first componentwise GR/QFT stress comparison.

The finite GR side is the checked normalized warped Einstein-matter fixture

    diag(1, -1, -1, -1).

If --qft-json is omitted, emit that exact target and an explicit
qft_component_data_missing status.  If a 4x4 QFT component matrix is supplied,
compute GR-QFT component residuals and classify exact zero/nonzero.

This is a diagnostic executable carrier, not SI calibration and not a theorem
that CMP119 stress admits this component representation.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path
from typing import Any

AXES = ["t", "x", "y", "z"]
GR = [
    [Fraction(1), Fraction(0), Fraction(0), Fraction(0)],
    [Fraction(0), Fraction(-1), Fraction(0), Fraction(0)],
    [Fraction(0), Fraction(0), Fraction(-1), Fraction(0)],
    [Fraction(0), Fraction(0), Fraction(0), Fraction(-1)],
]


def parse_fraction(value: Any) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        return Fraction(value)
    if isinstance(value, dict) and set(value) == {"num", "den"}:
        return Fraction(int(value["num"]), int(value["den"]))
    raise ValueError(f"unsupported rational component: {value!r}")


def parse_matrix(value: Any) -> list[list[Fraction]]:
    if not isinstance(value, list) or len(value) != 4:
        raise ValueError("QFT matrix must have four rows")
    rows: list[list[Fraction]] = []
    for row in value:
        if not isinstance(row, list) or len(row) != 4:
            raise ValueError("every QFT matrix row must have four entries")
        rows.append([parse_fraction(x) for x in row])
    return rows


SYMMETRIC_KEYS = ("00","01","02","03","11","12","13","22","23","33")


def expand_symmetric_components(value: Any) -> list[list[Fraction]]:
    if not isinstance(value, dict):
        raise ValueError("qft_symmetric_components must be an object")
    missing = [k for k in SYMMETRIC_KEYS if k not in value]
    if missing:
        raise ValueError(f"missing symmetric components: {missing}")
    c = {k: parse_fraction(value[k]) for k in SYMMETRIC_KEYS}
    return [
        [c["00"], c["01"], c["02"], c["03"]],
        [c["01"], c["11"], c["12"], c["13"]],
        [c["02"], c["12"], c["22"], c["23"]],
        [c["03"], c["13"], c["23"], c["33"]],
    ]


def sum_finite_d1_terms(value: Any) -> dict[str, Fraction]:
    """Sum the literal finite localized D1 contributions in each symmetric slot.

    This is the executable counterpart of the R142/R144 finite-sum carrier.
    It intentionally performs only exact rational summation; it does not
    manufacture the source terms or identify them with CMP116 derivatives.
    """
    if not isinstance(value, dict):
        raise ValueError("qft_finite_d1_terms must be an object")
    missing = [k for k in SYMMETRIC_KEYS if k not in value]
    if missing:
        raise ValueError(f"missing finite D1 slots: {missing}")
    sums: dict[str, Fraction] = {}
    for key in SYMMETRIC_KEYS:
        terms = value[key]
        if not isinstance(terms, list):
            raise ValueError(f"finite D1 slot {key} must be a list of rational terms")
        sums[key] = sum((parse_fraction(term) for term in terms), Fraction(0))
    return sums


def encoded(x: Fraction) -> int | str:
    if x.denominator == 1:
        return x.numerator
    return f"{x.numerator}/{x.denominator}"


def encode_matrix(matrix: list[list[Fraction]]) -> list[list[int | str]]:
    return [[encoded(x) for x in row] for row in matrix]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--qft-json", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()

    payload: dict[str, Any] = {
        "carrier": "normalized rational 4x4 stress components",
        "axes": AXES,
        "gr_target": encode_matrix(GR),
        "physical_si_calibration_claimed": False,
    }

    if args.qft_json is None:
        payload.update({
            "status": "qft_component_data_missing",
            "comparison_executed": False,
            "required_next_input":
                "ten CMP119/YM finite localized D1 sums (or their rational readouts) in symmetric slots 00,01,02,03,11,12,13,22,23,33",
        })
    else:
        raw = json.loads(args.qft_json.read_text())
        finite_d1_sums: dict[str, Fraction] | None = None
        if "qft_finite_d1_terms" in raw:
            finite_d1_sums = sum_finite_d1_terms(raw["qft_finite_d1_terms"])
            qft = expand_symmetric_components(finite_d1_sums)
            input_form = "ten finite localized D1 component sums"
        elif "qft_symmetric_components" in raw:
            qft = expand_symmetric_components(raw["qft_symmetric_components"])
            input_form = "ten symmetric components"
        else:
            qft = parse_matrix(raw["qft_stress"])
            input_form = "full 4x4 matrix"
        residual = [
            [GR[i][j] - qft[i][j] for j in range(4)]
            for i in range(4)
        ]
        flat = [abs(x) for row in residual for x in row]
        payload.update({
            "status": "exact_zero" if all(x == 0 for x in flat) else "nonzero_residual",
            "comparison_executed": True,
            "qft_stress": encode_matrix(qft),
            "input_form": input_form,
            "residual_gr_minus_qft": encode_matrix(residual),
            "l1_residual": encoded(sum(flat, Fraction(0))),
            "max_abs_residual": encoded(max(flat, default=Fraction(0))),
        })
        if finite_d1_sums is not None:
            payload["finite_d1_sums"] = {
                key: encoded(finite_d1_sums[key]) for key in SYMMETRIC_KEYS
            }

    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
