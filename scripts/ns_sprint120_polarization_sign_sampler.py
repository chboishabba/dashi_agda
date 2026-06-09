#!/usr/bin/env python3
"""Sprint 120 linear strain polarization sign sampler."""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint120_polarization_sign_sampler"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint120_polarization_sign_sampler")
SUMMARY_NAME = "ns_sprint120_polarization_sign_sampler_summary.json"
ROWS_NAME = "ns_sprint120_polarization_sign_sampler_rows.json"
CSV_NAME = "ns_sprint120_polarization_sign_sampler_rows.csv"
REPORT_NAME = "ns_sprint120_polarization_sign_sampler.md"

C_VALUE = 1.0
ANGLE_SAMPLES = (
    ("0", 0.0),
    ("pi/8", math.pi / 8.0),
    ("pi/4", math.pi / 4.0),
    ("3pi/8", 3.0 * math.pi / 8.0),
    ("pi/2", math.pi / 2.0),
    ("5pi/8", 5.0 * math.pi / 8.0),
    ("3pi/4", 3.0 * math.pi / 4.0),
    ("7pi/8", 7.0 * math.pi / 8.0),
    ("pi", math.pi),
)
TOLERANCE = 1.0e-12


@dataclass(frozen=True)
class PolarizationSignRow:
    theta_label: str
    theta_radians: float
    k_x: float
    k_y: float
    n_x: float
    n_y: float
    strain_xx: float
    strain_xy: float
    strain_yx: float
    strain_yy: float
    q: float
    flux_proxy: float
    amplification_proxy: float
    anticorrelation_product: float
    anticorrelation_nonpositive: bool
    positive_flux: bool
    negative_amplification: bool

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def clean(value: float) -> float:
    if abs(value) < TOLERANCE:
        return 0.0
    return value


def build_rows(c_value: float = C_VALUE) -> list[PolarizationSignRow]:
    rows: list[PolarizationSignRow] = []
    for theta_label, theta in ANGLE_SAMPLES:
        cos_theta = clean(math.cos(theta))
        sin_theta = clean(math.sin(theta))
        k_x = cos_theta
        k_y = sin_theta
        n_x = -sin_theta
        n_y = cos_theta
        strain_xx = -c_value
        strain_xy = 0.0
        strain_yx = 0.0
        strain_yy = c_value
        q = clean(n_x * strain_xx * n_x + n_y * strain_yy * n_y)
        flux_proxy = q
        amplification_proxy = clean(-q)
        anticorrelation_product = clean(flux_proxy * amplification_proxy)
        rows.append(
            PolarizationSignRow(
                theta_label=theta_label,
                theta_radians=theta,
                k_x=k_x,
                k_y=k_y,
                n_x=n_x,
                n_y=n_y,
                strain_xx=strain_xx,
                strain_xy=strain_xy,
                strain_yx=strain_yx,
                strain_yy=strain_yy,
                q=q,
                flux_proxy=flux_proxy,
                amplification_proxy=amplification_proxy,
                anticorrelation_product=anticorrelation_product,
                anticorrelation_nonpositive=anticorrelation_product <= TOLERANCE,
                positive_flux=flux_proxy > TOLERANCE,
                negative_amplification=amplification_proxy < -TOLERANCE,
            )
        )
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        raise ValueError("cannot write empty row set")
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0].keys()))
        writer.writeheader()
        writer.writerows(rows)


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "theta",
        "q = n.e.n",
        "flux proxy",
        "amplification proxy",
        "product",
        "product <= 0",
    )
    keys = (
        "theta_label",
        "q",
        "flux_proxy",
        "amplification_proxy",
        "anticorrelation_product",
        "anticorrelation_nonpositive",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    positive_flux_rows = [row for row in rows if row["positive_flux"]]
    return {
        "contract": CONTRACT,
        "row_count": len(rows),
        "c_value": C_VALUE,
        "angle_labels": [label for label, _theta in ANGLE_SAMPLES],
        "k_formula": "(cos theta, sin theta)",
        "n_formula": "(-sin theta, cos theta)",
        "strain_matrix": [[-C_VALUE, 0.0], [0.0, C_VALUE]],
        "q_formula": "n.e.n = -C*sin(theta)^2 + C*cos(theta)^2",
        "flux_proxy_formula": "q",
        "amplification_proxy_formula": "-q",
        "anticorrelation_product_formula": "flux_proxy * amplification_proxy = -q^2",
        "positive_flux_row_count": len(positive_flux_rows),
        "anticorrelation_all_rows": all(row["anticorrelation_nonpositive"] for row in rows),
        "positive_flux_rows_have_negative_amplification": all(
            row["negative_amplification"] for row in positive_flux_rows
        ),
        "constant_linear_strain_route_obstructed": True,
        "linear_strain_algebra_corrected": True,
        "clay": False,
        "complete": True,
        "exit_code": 0,
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    text = "\n".join(
        (
            f"# {CONTRACT}",
            "",
            "Deterministic sampler for the corrected linear strain sign algebra.",
            "",
            "Formula surface:",
            "",
            "- k = (cos theta, sin theta)",
            "- n = (-sin theta, cos theta)",
            "- e = diag(-C, +C)",
            "- q = n.e.n",
            "- flux_proxy = q",
            "- amplification_proxy = -q",
            "- flux_proxy * amplification_proxy = -q^2 <= 0",
            "",
            "Summary:",
            "",
            f"- anticorrelation_all_rows: {format_value(summary['anticorrelation_all_rows'])}",
            "- positive_flux_rows_have_negative_amplification: "
            f"{format_value(summary['positive_flux_rows_have_negative_amplification'])}",
            "- constant_linear_strain_route_obstructed: "
            f"{format_value(summary['constant_linear_strain_route_obstructed'])}",
            f"- clay: {format_value(summary['clay'])}",
            "",
            markdown_table(rows),
            "",
        )
    )
    path.write_text(text, encoding="utf-8")


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = [row.as_row() for row in build_rows()]
    summary = build_summary(rows)

    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_csv(out_dir / CSV_NAME, rows)
    write_report(out_dir / REPORT_NAME, summary, rows)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
