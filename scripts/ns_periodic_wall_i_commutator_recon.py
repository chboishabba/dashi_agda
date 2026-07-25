#!/usr/bin/env python3
"""Exact finite reconnaissance for the Wall-I far-low commutator kernel.

The script compares three literal Fourier objects on the frozen periodic carrier:

* K_raw     = m_j(k) B(k,p,q),
* K_diff    = (m_j(k)-m_j(q)) B(k,p,q),
* K_absdiff = |m_j(k)-m_j(q)| |B(k,p,q)|.

K_diff retains every rational sign in the derivative/Leray/Biot--Savart tensor.
K_absdiff is used for the honest absolute Schur diagnostic.  Signed aggregation
is reported separately and is never called a Schur norm.  Every result is a
finite-cutoff research certificate, not a cutoff-uniform PDE proof.
"""
from __future__ import annotations

import argparse
import csv
import json
from collections import defaultdict
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import DefaultDict, Dict, List, Mapping, Sequence, Tuple

from ns_periodic_wall_i_lab import (
    Mode,
    biot_savart_cross_matrix,
    classify_triad,
    dyadic_level,
    dyadic_level_from_radius,
    dyadic_weight,
    hat_multiplier,
    iter_target_triads,
    leray_matrix,
    rho,
)

Tensor = Tuple[Tuple[Tuple[Fraction, Fraction, Fraction], ...], ...]
FlatTensor = Tuple[Fraction, ...]


def tensor_flatten(tensor: Tensor) -> FlatTensor:
    return tuple(tensor[i][a][b] for i in range(3) for a in range(3) for b in range(3))


def tensor_scale(factor: Fraction, tensor: Tensor) -> Tensor:
    return tuple(
        tuple(
            tuple(factor * tensor[i][a][b] for b in range(3))
            for a in range(3)
        )
        for i in range(3)
    )


def tensor_absolute(tensor: Tensor) -> Tensor:
    return tuple(
        tuple(tuple(abs(tensor[i][a][b]) for b in range(3)) for a in range(3))
        for i in range(3)
    )


def tensor_l1(tensor: Tensor) -> Fraction:
    return sum((abs(value) for value in tensor_flatten(tensor)), Fraction(0))


def tensor_add_flat(left: Sequence[Fraction], right: FlatTensor) -> FlatTensor:
    return tuple(left[i] + right[i] for i in range(27))


def far_low_bilinear_symbol(
    low: Mode,
    high: Mode,
    output: Mode,
    output_shell: int,
    weight_exponent: int,
) -> Tensor:
    """Literal real coefficient tensor for the far-low placement.

    The low coefficient is first converted by the real Biot--Savart cross
    matrix.  It is contracted with the high derivative frequency, then the
    high vector is projected by the output Leray matrix.  Global powers of i
    have unit modulus and are common to every entry, so the rational real tensor
    retains the relevant relative signs.
    """
    cross = biot_savart_cross_matrix(low)
    projection = leray_matrix(output)
    directional = tuple(
        sum((Fraction(high[c]) * cross[c][a] for c in range(3)), Fraction(0))
        for a in range(3)
    )
    high_level = max(0, dyadic_level(high))
    ratio = dyadic_weight(output_shell - high_level, weight_exponent)
    return tuple(
        tuple(
            tuple(ratio * projection[i][b] * directional[a] for b in range(3))
            for a in range(3)
        )
        for i in range(3)
    )


@dataclass(frozen=True)
class KernelTriple:
    raw: Tensor
    difference: Tensor
    absolute_difference: Tensor
    raw_factor: Fraction
    difference_factor: Fraction


def far_low_kernel_triple(
    low: Mode,
    high: Mode,
    output: Mode,
    output_shell: int,
    weight_exponent: int,
) -> KernelTriple:
    symbol = far_low_bilinear_symbol(low, high, output, output_shell, weight_exponent)
    raw_factor = hat_multiplier(output_shell, rho(output))
    input_factor = hat_multiplier(output_shell, rho(high))
    difference_factor = raw_factor - input_factor
    difference = tensor_scale(difference_factor, symbol)
    return KernelTriple(
        raw=tensor_scale(raw_factor, symbol),
        difference=difference,
        absolute_difference=tensor_absolute(difference),
        raw_factor=raw_factor,
        difference_factor=difference_factor,
    )


@dataclass
class AbsoluteSchurStats:
    row_count: int
    column_count: int
    nonzero_entries: int
    row_max: str
    row_argmax: Mode | None
    column_max: str
    column_argmax: Mode | None
    product: str
    product_float: float


@dataclass
class SignedAggregationStats:
    row_max: str
    row_argmax: Mode | None
    column_max: str
    column_argmax: Mode | None
    row_cancellation_ratio: float | None
    column_cancellation_ratio: float | None


@dataclass
class CommutatorReconReport:
    cutoff: int
    output_shell: int
    separation: int
    overlap: int
    weight_exponent: int
    target_separation: int
    max_cutoff_level: int
    target_separation_geometrically_accessible: bool
    supported_far_low_triads: int
    exact_complete: bool
    raw_absolute_schur: AbsoluteSchurStats
    absolute_difference_schur: AbsoluteSchurStats
    difference_signed_aggregation: SignedAggregationStats
    sample_factors: List[Dict[str, object]]


def _absolute_stats(
    rows: Mapping[Mode, Fraction],
    columns: Mapping[Mode, Fraction],
    nonzero: int,
) -> AbsoluteSchurStats:
    if rows:
        row_argmax, row_max = max(rows.items(), key=lambda item: item[1])
    else:
        row_argmax, row_max = None, Fraction(0)
    if columns:
        column_argmax, column_max = max(columns.items(), key=lambda item: item[1])
    else:
        column_argmax, column_max = None, Fraction(0)
    product = row_max * column_max
    return AbsoluteSchurStats(
        row_count=len(rows),
        column_count=len(columns),
        nonzero_entries=nonzero,
        row_max=str(row_max),
        row_argmax=row_argmax,
        column_max=str(column_max),
        column_argmax=column_argmax,
        product=str(product),
        product_float=float(product),
    )


def _signed_max(aggregates: Mapping[Mode, Sequence[Fraction]]) -> Tuple[Mode | None, Fraction]:
    if not aggregates:
        return None, Fraction(0)
    values = {
        key: sum((abs(component) for component in vector), Fraction(0))
        for key, vector in aggregates.items()
    }
    return max(values.items(), key=lambda item: item[1])


def commutator_recon_report(
    cutoff: int,
    output_shell: int,
    separation: int,
    overlap: int,
    weight_exponent: int,
    target_separation: int,
    max_entries: int,
    sample_limit: int = 8,
) -> CommutatorReconReport:
    raw_rows: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    raw_columns: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    diff_rows: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    diff_columns: DefaultDict[Mode, Fraction] = defaultdict(Fraction)
    signed_rows: Dict[Mode, FlatTensor] = {}
    signed_columns: Dict[Mode, FlatTensor] = {}

    supported = 0
    raw_nonzero = 0
    diff_nonzero = 0
    exact_complete = True
    samples: List[Dict[str, object]] = []

    for p, q, k in iter_target_triads(cutoff, output_shell):
        lane = classify_triad(p, q, output_shell, separation, overlap)
        if lane == "far-low-left":
            low, high = p, q
        elif lane == "far-low-right":
            low, high = q, p
        else:
            continue
        supported += 1
        if supported > max_entries:
            exact_complete = False
            break

        triple = far_low_kernel_triple(
            low, high, k, output_shell, weight_exponent
        )
        raw_norm = tensor_l1(triple.raw)
        diff_norm = tensor_l1(triple.absolute_difference)

        if raw_norm:
            raw_nonzero += 1
            raw_rows[k] += raw_norm
            raw_columns[low] += raw_norm
        if diff_norm:
            diff_nonzero += 1
            diff_rows[k] += diff_norm
            diff_columns[low] += diff_norm
            flat = tensor_flatten(triple.difference)
            signed_rows[k] = tensor_add_flat(
                signed_rows.get(k, (Fraction(0),) * 27), flat
            )
            signed_columns[low] = tensor_add_flat(
                signed_columns.get(low, (Fraction(0),) * 27), flat
            )

        if len(samples) < sample_limit and (raw_norm or diff_norm):
            samples.append(
                {
                    "low": low,
                    "high": high,
                    "output": k,
                    "raw_factor": str(triple.raw_factor),
                    "difference_factor": str(triple.difference_factor),
                    "raw_tensor_l1": str(raw_norm),
                    "absolute_difference_tensor_l1": str(diff_norm),
                }
            )

    raw_stats = _absolute_stats(raw_rows, raw_columns, raw_nonzero)
    diff_stats = _absolute_stats(diff_rows, diff_columns, diff_nonzero)
    signed_row_argmax, signed_row_max = _signed_max(signed_rows)
    signed_col_argmax, signed_col_max = _signed_max(signed_columns)

    signed = SignedAggregationStats(
        row_max=str(signed_row_max),
        row_argmax=signed_row_argmax,
        column_max=str(signed_col_max),
        column_argmax=signed_col_argmax,
        row_cancellation_ratio=(
            float(signed_row_max / Fraction(diff_stats.row_max))
            if Fraction(diff_stats.row_max) != 0
            else None
        ),
        column_cancellation_ratio=(
            float(signed_col_max / Fraction(diff_stats.column_max))
            if Fraction(diff_stats.column_max) != 0
            else None
        ),
    )

    max_level = dyadic_level_from_radius(cutoff)
    target_accessible = (
        output_shell >= target_separation
        and max_level >= output_shell
    )

    return CommutatorReconReport(
        cutoff=cutoff,
        output_shell=output_shell,
        separation=separation,
        overlap=overlap,
        weight_exponent=weight_exponent,
        target_separation=target_separation,
        max_cutoff_level=max_level,
        target_separation_geometrically_accessible=target_accessible,
        supported_far_low_triads=supported,
        exact_complete=exact_complete,
        raw_absolute_schur=raw_stats,
        absolute_difference_schur=diff_stats,
        difference_signed_aggregation=signed,
        sample_factors=samples,
    )


def write_csv(path: Path, report: CommutatorReconReport) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "kernel",
                "row_max",
                "column_max",
                "product",
                "product_float",
                "nonzero_entries",
            ]
        )
        writer.writerow(
            [
                "raw_absolute",
                report.raw_absolute_schur.row_max,
                report.raw_absolute_schur.column_max,
                report.raw_absolute_schur.product,
                report.raw_absolute_schur.product_float,
                report.raw_absolute_schur.nonzero_entries,
            ]
        )
        writer.writerow(
            [
                "absolute_difference",
                report.absolute_difference_schur.row_max,
                report.absolute_difference_schur.column_max,
                report.absolute_difference_schur.product,
                report.absolute_difference_schur.product_float,
                report.absolute_difference_schur.nonzero_entries,
            ]
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=4)
    parser.add_argument("--output-shell", type=int, default=2)
    parser.add_argument("--separation", type=int, default=2)
    parser.add_argument("--target-separation", type=int, default=8)
    parser.add_argument("--overlap", type=int, default=1)
    parser.add_argument("--weight-exponent", type=int, default=1)
    parser.add_argument("--max-entries", type=int, default=2_000_000)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--csv-out", type=Path)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if min(
        args.cutoff,
        args.output_shell,
        args.separation,
        args.target_separation,
        args.overlap,
    ) < 0:
        raise SystemExit("cutoff, shells, separations and overlap must be nonnegative")

    report = commutator_recon_report(
        cutoff=args.cutoff,
        output_shell=args.output_shell,
        separation=args.separation,
        overlap=args.overlap,
        weight_exponent=args.weight_exponent,
        target_separation=args.target_separation,
        max_entries=args.max_entries,
    )
    findings = [
        "K_diff retains the literal signed multiplier difference before any norm estimate.",
        "The absolute-difference Schur product tests whether the commutator gain alone survives absolute majorisation.",
        "Signed aggregation is a cancellation diagnostic, not a Schur norm or proof of an operator estimate.",
        "A target R=8 run is meaningful only when the finite cutoff and output shell can contain a nonzero low shell separated by eight levels.",
        "Every reported quantity is finite-cutoff reconnaissance and cannot inhabit a cutoff-uniform Agda theorem.",
    ]
    payload = {
        "status": "research-certificate-not-proof",
        "kernel_definitions": {
            "raw": "m_j(k) * B(k,p,q)",
            "difference": "(m_j(k)-m_j(q)) * B(k,p,q)",
            "absolute_difference": "abs(m_j(k)-m_j(q)) * abs(B(k,p,q))",
        },
        "report": asdict(report),
        "findings": findings,
    }
    text = json.dumps(payload, indent=2, sort_keys=True, default=list)
    print(text)
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(text + "\n", encoding="utf-8")
    if args.csv_out:
        write_csv(args.csv_out, report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
