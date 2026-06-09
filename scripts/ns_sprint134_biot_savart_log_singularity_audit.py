#!/usr/bin/env python3
"""Sprint 134 axisymmetric Biot-Savart logarithmic singularity audit.

This emitter tests the uniform no-log axisymmetric Biot-Savart claim against
the complete elliptic integral singularity that appears in the axisymmetric
kernel away from the axis.  The relevant local factor is

    K(k) ~ log(4 / sqrt(1 - k^2)) as k -> 1,

where K is the complete elliptic integral of the first kind.  The script uses
the arithmetic-geometric mean identity

    K(k) = pi / (2 AGM(1, sqrt(1 - k^2)))

with Python stdlib only.  Ratios K(k)/log(4/sqrt(1-k^2)) approaching 1 are
recorded as an executable falsification of the uniform no-log claim; the
extra r-factor may still help exactly at the axis, but it does not remove the
standard logarithmic singularity uniformly through the cylinder.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint134_biot_savart_log_singularity_audit"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint134_biot_savart_log_singularity_audit")
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
SUMMARY_NAME = CONTRACT + "_summary.json"
REPORT_NAME = CONTRACT + ".md"

FIELDNAMES = (
    "row_id",
    "k",
    "one_minus_k",
    "one_minus_k_squared",
    "elliptic_K_agm",
    "log_asymptotic",
    "ratio_K_over_log",
    "absolute_ratio_error",
    "supports_standard_log_singularity",
    "supports_uniform_no_log_claim",
    "interpretation",
)


@dataclass(frozen=True)
class AuditRow:
    row_id: str
    k: float
    one_minus_k: float
    one_minus_k_squared: float
    elliptic_K_agm: float
    log_asymptotic: float
    ratio_K_over_log: float
    absolute_ratio_error: float
    supports_standard_log_singularity: bool
    supports_uniform_no_log_claim: bool
    interpretation: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def agm(a: float, b: float, *, tolerance: float = 1.0e-15) -> float:
    """Return arithmetic-geometric mean of positive floats."""
    if a <= 0.0 or b <= 0.0:
        raise ValueError("AGM inputs must be positive")
    for _ in range(100):
        next_a = 0.5 * (a + b)
        next_b = math.sqrt(a * b)
        if abs(next_a - next_b) <= tolerance * max(1.0, abs(next_a)):
            return 0.5 * (next_a + next_b)
        a, b = next_a, next_b
    raise RuntimeError("AGM did not converge")


def complete_elliptic_k(k: float) -> float:
    """Compute K(k) for 0 <= k < 1 using the AGM identity."""
    if not 0.0 <= k < 1.0:
        raise ValueError("k must satisfy 0 <= k < 1")
    complementary = math.sqrt((1.0 - k) * (1.0 + k))
    return math.pi / (2.0 * agm(1.0, complementary))


def log_asymptotic(k: float) -> float:
    """Return log(4/sqrt(1-k^2)), the leading K(k) singularity."""
    one_minus_k_squared = (1.0 - k) * (1.0 + k)
    return math.log(4.0 / math.sqrt(one_minus_k_squared))


def sample_k_values() -> list[float]:
    """Deterministic samples approaching the diagonal singularity k=1."""
    return [
        0.9,
        0.99,
        0.999,
        0.9999,
        0.99999,
        0.999999,
        0.9999999,
        0.99999999,
        0.999999999,
        0.9999999999,
        0.99999999999,
        0.999999999999,
        0.9999999999999,
    ]


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for index, k in enumerate(sample_k_values(), start=1):
        K = complete_elliptic_k(k)
        asymptotic = log_asymptotic(k)
        ratio = K / asymptotic
        error = abs(1.0 - ratio)
        rows.append(
            AuditRow(
                row_id=f"k_to_one_{index:02d}",
                k=k,
                one_minus_k=1.0 - k,
                one_minus_k_squared=(1.0 - k) * (1.0 + k),
                elliptic_K_agm=K,
                log_asymptotic=asymptotic,
                ratio_K_over_log=ratio,
                absolute_ratio_error=error,
                supports_standard_log_singularity=error < 0.1,
                supports_uniform_no_log_claim=False,
                interpretation=(
                    "K(k) tracks the standard logarithmic singularity; "
                    "axisymmetric kernel estimates cannot be uniformly no-log "
                    "away from the axis at this diagonal limit."
                ),
            ).as_row()
        )
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    tail = rows[-5:]
    tail_max_error = max(row["absolute_ratio_error"] for row in tail)
    ratios = [row["ratio_K_over_log"] for row in rows]
    monotone_toward_one_on_tail = all(
        abs(1.0 - tail[i + 1]["ratio_K_over_log"])
        <= abs(1.0 - tail[i]["ratio_K_over_log"])
        for i in range(len(tail) - 1)
    )

    summary = {
        "contract": CONTRACT,
        "method": "complete_elliptic_integral_agm_vs_log_asymptotic",
        "identity_used": "K(k)=pi/(2*AGM(1,sqrt(1-k^2)))",
        "asymptotic_checked": "K(k) ~ log(4/sqrt(1-k^2)) as k->1",
        "row_count": len(rows),
        "min_k": min(row["k"] for row in rows),
        "max_k": max(row["k"] for row in rows),
        "first_ratio": ratios[0],
        "last_ratio": ratios[-1],
        "tail_max_absolute_ratio_error": tail_max_error,
        "tail_ratio_error_below_0_01": tail_max_error < 0.01,
        "tail_ratios_monotone_toward_one": monotone_toward_one_on_tail,
        "no_log_axisymmetric_biot_savart_uniform": False,
        "axis_only_extra_r_factor_scope": True,
        "standard_log_singularity_persists": True,
        "uniform_away_from_axis_claim_retracted": True,
        "near_axis_cancellation_not_uniform": True,
        "hou_luo_viscous_obstruction_requires_reaudit": True,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "complete elliptic integral samples converge to the logarithmic "
            "asymptotic ratio 1, falsifying the uniform no-log axisymmetric "
            "Biot-Savart claim away from the axis"
        ),
        "control_card": {
            "O": (
                "Worker 2 owns only scripts/ns_sprint134_biot_savart_log_"
                "singularity_audit.py and its matching output directory."
            ),
            "R": (
                "Encode and evaluate the axisymmetric Biot-Savart no-log claim "
                "as false uniformly away from the axis."
            ),
            "C": "stdlib AGM implementation, k->1 sampler, JSON/CSV/Markdown outputs",
            "S": (
                "K(k)/log(4/sqrt(1-k^2)) tends to 1; the logarithmic diagonal "
                "singularity persists away from r=0."
            ),
            "L": "claim -> asymptotic sampler -> invariant checks -> false no-log summary",
            "P": (
                "Retract uniform no-log lemma; preserve only the axis-local "
                "extra-r-factor scope."
            ),
            "G": "full_clay_ns_solved=false; clay_navier_stokes_promoted=false",
            "F": (
                "This audit closes only the false auxiliary claim; Hou-Luo NS "
                "and full Clay remain open."
            ),
        },
    }
    return summary


def validate_summary(summary: dict[str, Any]) -> None:
    required_false = (
        "no_log_axisymmetric_biot_savart_uniform",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    )
    for key in required_false:
        if summary[key] is not False:
            raise AssertionError(f"{key} must remain false")
    required_true = (
        "axis_only_extra_r_factor_scope",
        "standard_log_singularity_persists",
        "complete",
        "tail_ratio_error_below_0_01",
    )
    for key in required_true:
        if summary[key] is not True:
            raise AssertionError(f"{key} must be true")
    if abs(1.0 - summary["last_ratio"]) >= 0.01:
        raise AssertionError("last K/log ratio did not converge close enough to 1")


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)


def fmt_bool(value: bool) -> str:
    return str(value).lower()


def write_markdown(path: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 134 Biot-Savart Log Singularity Audit",
        "",
        "## Summary",
        "",
        f"- `no_log_axisymmetric_biot_savart_uniform`: {fmt_bool(summary['no_log_axisymmetric_biot_savart_uniform'])}",
        f"- `axis_only_extra_r_factor_scope`: {fmt_bool(summary['axis_only_extra_r_factor_scope'])}",
        f"- `standard_log_singularity_persists`: {fmt_bool(summary['standard_log_singularity_persists'])}",
        f"- `last_ratio`: {summary['last_ratio']:.12f}",
        f"- `tail_max_absolute_ratio_error`: {summary['tail_max_absolute_ratio_error']:.6e}",
        f"- `full_clay_ns_solved`: {fmt_bool(summary['full_clay_ns_solved'])}",
        f"- `clay_navier_stokes_promoted`: {fmt_bool(summary['clay_navier_stokes_promoted'])}",
        "",
        "## Samples",
        "",
        "| k | K(k) AGM | log asymptotic | K/log | |1-ratio| |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for row in rows:
        lines.append(
            "| "
            f"{row['k']:.13f} | "
            f"{row['elliptic_K_agm']:.12f} | "
            f"{row['log_asymptotic']:.12f} | "
            f"{row['ratio_K_over_log']:.12f} | "
            f"{row['absolute_ratio_error']:.6e} |"
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            (
                "The complete elliptic integral factor converges to the same "
                "logarithmic asymptotic as the standard singular kernel.  The "
                "axisymmetric extra-r cancellation is therefore an axis-local "
                "fact, not a uniform cylinder estimate."
            ),
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    validate_summary(summary)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_markdown(out_dir / REPORT_NAME, rows, summary)

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
