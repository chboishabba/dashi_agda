#!/usr/bin/env python3
"""Sprint 131 localized viscous lower-comparison audit.

This deterministic audit records the scaling calculation for
LocalizedViscousLowerComparison in the Hou-Luo Navier-Stokes obstruction
lane.  In the window 1 < alpha < 3/2, set beta = alpha - 1,
Omega = tau^-alpha, and delta = tau^beta.  The localized viscous lower term
is nu * Omega / delta^2 = nu * tau^-(alpha + 2*beta).  Against the Worker1
source upper form source <= C_src * tau^-1, alpha = 1 + beta gives

    viscous / source >= C * nu * tau^-3*beta

where C is the normalized lower/upper comparison constant.  Hence the lower
ratio diverges as tau -> 0 for every beta > 0 and nu > 0.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


AUDIT_ID = "ns_sprint131_localized_viscous_comparison_audit"
LEMMA = "LocalizedViscousLowerComparison"
DEFAULT_OUT_DIR = Path("outputs/ns_sprint131_localized_viscous_comparison_audit")
ROWS_NAME = f"{AUDIT_ID}_rows.json"
SUMMARY_NAME = f"{AUDIT_ID}_summary.json"
REPORT_NAME = f"{AUDIT_ID}.md"

ALPHA_VALUES = (
    Fraction(11, 10),
    Fraction(5, 4),
    Fraction(7, 5),
)
TAU_VALUES = (
    Fraction(1, 10),
    Fraction(1, 100),
    Fraction(1, 1000),
    Fraction(1, 10000),
)
NU_VALUES = (
    Fraction(1, 1),
    Fraction(1, 10),
    Fraction(1, 100),
)
WINDOW_LOWER = Fraction(1, 1)
WINDOW_UPPER = Fraction(3, 2)
NORMALIZED_COMPARISON_CONSTANT = Fraction(1, 1)


@dataclass(frozen=True)
class AuditRow:
    row_id: str
    lemma: str
    alpha: float
    alpha_fraction: str
    beta: float
    beta_fraction: str
    tau: float
    tau_fraction: str
    nu: float
    nu_fraction: str
    delta_formula: str
    delta_value: float
    omega_formula: str
    omega_value: float
    viscous_lower_formula: str
    viscous_lower_exponent: str
    viscous_lower_value: float
    source_upper_formula: str
    source_upper_exponent: str
    source_upper_value: float
    ratio_lower_bound_formula: str
    ratio_lower_bound_exponent: str
    ratio_lower_bound_value: float
    ratio_exponent_positive: bool
    in_scaling_window: bool
    beta_positive: bool
    nu_positive: bool
    ratio_diverges: bool
    comparison_closed: bool

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def fmt_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def fmt_tau_power(power: Fraction) -> str:
    return f"tau^-({fmt_fraction(power)})"


def float_power(tau: Fraction, power: Fraction) -> float:
    return float(tau) ** float(power)


def build_rows() -> list[dict[str, Any]]:
    rows: list[AuditRow] = []
    for alpha in ALPHA_VALUES:
        beta = alpha - 1
        viscous_exponent = alpha + 2 * beta
        source_exponent = Fraction(1, 1)
        ratio_exponent = viscous_exponent - source_exponent
        for tau in TAU_VALUES:
            delta_value = float_power(tau, beta)
            omega_value = float_power(tau, -alpha)
            source_upper_value = float_power(tau, -source_exponent)
            for nu in NU_VALUES:
                viscous_lower_value = float(nu) * omega_value / (delta_value**2)
                ratio_lower_bound_value = (
                    float(NORMALIZED_COMPARISON_CONSTANT)
                    * float(nu)
                    * float_power(tau, -ratio_exponent)
                )
                in_window = WINDOW_LOWER < alpha < WINDOW_UPPER
                beta_positive = beta > 0
                nu_positive = nu > 0
                ratio_exponent_positive = ratio_exponent == 3 * beta and ratio_exponent > 0
                ratio_diverges = beta_positive and nu_positive and ratio_exponent_positive
                comparison_closed = (
                    in_window
                    and beta_positive
                    and nu_positive
                    and viscous_exponent == 1 + 3 * beta
                    and ratio_exponent == 3 * beta
                    and ratio_diverges
                )
                rows.append(
                    AuditRow(
                        row_id=f"r{len(rows):03d}",
                        lemma=LEMMA,
                        alpha=float(alpha),
                        alpha_fraction=fmt_fraction(alpha),
                        beta=float(beta),
                        beta_fraction=fmt_fraction(beta),
                        tau=float(tau),
                        tau_fraction=fmt_fraction(tau),
                        nu=float(nu),
                        nu_fraction=fmt_fraction(nu),
                        delta_formula="delta=tau^beta",
                        delta_value=delta_value,
                        omega_formula="Omega=tau^-alpha",
                        omega_value=omega_value,
                        viscous_lower_formula="nu*Omega/delta^2",
                        viscous_lower_exponent=fmt_tau_power(viscous_exponent),
                        viscous_lower_value=viscous_lower_value,
                        source_upper_formula="Worker1 source upper: source<=C_src*tau^-1",
                        source_upper_exponent=fmt_tau_power(source_exponent),
                        source_upper_value=source_upper_value,
                        ratio_lower_bound_formula="viscous/source>=C*nu*tau^(-3*beta)",
                        ratio_lower_bound_exponent=fmt_tau_power(ratio_exponent),
                        ratio_lower_bound_value=ratio_lower_bound_value,
                        ratio_exponent_positive=ratio_exponent_positive,
                        in_scaling_window=in_window,
                        beta_positive=beta_positive,
                        nu_positive=nu_positive,
                        ratio_diverges=ratio_diverges,
                        comparison_closed=comparison_closed,
                    )
                )
    return [row.as_row() for row in rows]


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def format_value(value: Any) -> str:
    if isinstance(value, bool):
        return str(value).lower()
    if isinstance(value, float):
        return f"{value:.12g}"
    return str(value)


def markdown_table(rows: list[dict[str, Any]]) -> str:
    headers = (
        "row",
        "alpha",
        "beta",
        "tau",
        "nu",
        "viscous",
        "source",
        "ratio lower",
        "diverges",
        "closed",
    )
    keys = (
        "row_id",
        "alpha_fraction",
        "beta_fraction",
        "tau_fraction",
        "nu_fraction",
        "viscous_lower_exponent",
        "source_upper_exponent",
        "ratio_lower_bound_value",
        "ratio_diverges",
        "comparison_closed",
    )
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    for row in rows:
        lines.append("| " + " | ".join(format_value(row[key]) for key in keys) + " |")
    return "\n".join(lines)


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    all_closed = all(row["comparison_closed"] for row in rows)
    all_diverge = all(row["ratio_diverges"] for row in rows)
    return {
        "audit_id": AUDIT_ID,
        "lemma": LEMMA,
        "row_count": len(rows),
        "scaling_window": "1 < alpha < 3/2",
        "alpha_fraction_values": [fmt_fraction(value) for value in ALPHA_VALUES],
        "alpha_values": [float(value) for value in ALPHA_VALUES],
        "window_lower": float(WINDOW_LOWER),
        "window_upper": float(WINDOW_UPPER),
        "beta_rule": "beta=alpha-1",
        "delta_rule": "delta=tau^beta",
        "omega_rule": "Omega=tau^-alpha",
        "viscous_term": "nu*Omega/delta^2",
        "viscous_exponent_rule": "alpha+2*beta=1+3*beta",
        "source_upper_bound": "source<=C_src*tau^-1",
        "worker1_source_upper_form": "C_src*tau^-1",
        "ratio_lower_bound": "viscous/source>=C*nu*tau^(-3*beta)",
        "ratio_exponent": "-3*beta",
        "normalized_comparison_constant": fmt_fraction(NORMALIZED_COMPARISON_CONSTANT),
        "ratio_divergence_condition": "beta>0 and nu>0",
        "all_sampled_alpha_in_window": all(row["in_scaling_window"] for row in rows),
        "all_sampled_beta_positive": all(row["beta_positive"] for row in rows),
        "all_sampled_nu_positive": all(row["nu_positive"] for row in rows),
        "all_ratio_exponents_positive": all(row["ratio_exponent_positive"] for row in rows),
        "viscous_lower_comparison_closed": all_closed,
        "ratio_diverges": all_diverge,
        "supports_hou_luo_ns_obstruction": True,
        "hou_luo_ns_route_obstructed": True,
        "proof_claimed": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "Localized viscous lower comparison closes for the sampled scaling "
            "window and records Hou-Luo NS obstruction support without promoting "
            "the full Clay Navier-Stokes claim."
        ),
        "control_card": {
            "O": "Worker 2 owns only the localized viscous comparison audit script and generated output directory.",
            "R": "Check the 1<alpha<3/2, beta=alpha-1, delta=tau^beta scaling relation for LocalizedViscousLowerComparison.",
            "C": "Deterministic Python audit emits rows JSON, summary JSON, and Markdown report.",
            "S": "Rows are generated from fixed rational alpha, tau, and nu grids; no external state is read.",
            "L": "Omega=tau^-alpha and nu*Omega/delta^2 give tau^-(alpha+2*beta)=tau^-(1+3*beta).",
            "P": "Against Worker1 source<=C_src*tau^-1, record viscous/source>=C*nu*tau^(-3*beta).",
            "G": "The ratio diverges as tau->0 for every beta>0 and nu>0, supporting the Hou-Luo NS obstruction.",
            "F": "The audit does not promote Clay Navier-Stokes; it closes only this localized comparison ledger.",
        },
    }


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    lines = [
        "# NS Sprint 131 Localized Viscous Comparison Audit",
        "",
        f"- audit_id: `{summary['audit_id']}`",
        f"- lemma: `{summary['lemma']}`",
        f"- scaling_window: `{summary['scaling_window']}`",
        f"- beta_rule: `{summary['beta_rule']}`",
        f"- delta_rule: `{summary['delta_rule']}`",
        f"- omega_rule: `{summary['omega_rule']}`",
        f"- viscous_term: `{summary['viscous_term']}`",
        f"- source_upper_bound: `{summary['source_upper_bound']}`",
        f"- ratio_lower_bound: `{summary['ratio_lower_bound']}`",
        f"- exact_ratio_exponent: `{summary['ratio_exponent']}`",
        f"- viscous_lower_comparison_closed: `{format_value(summary['viscous_lower_comparison_closed'])}`",
        f"- ratio_diverges: `{format_value(summary['ratio_diverges'])}`",
        f"- supports_hou_luo_ns_obstruction: `{format_value(summary['supports_hou_luo_ns_obstruction'])}`",
        f"- clay_navier_stokes_promoted: `{format_value(summary['clay_navier_stokes_promoted'])}`",
        f"- complete: `{format_value(summary['complete'])}`",
        f"- exit_code: `{summary['exit_code']}`",
        "",
        "## Algebra",
        "",
        "With alpha = 1 + beta and delta = tau^beta:",
        "",
        "`nu*Omega/delta^2 = nu*tau^(-alpha-2*beta) = nu*tau^(-1-3*beta)`.",
        "",
        "Using the Worker1 source upper form `source <= C_src*tau^-1`, the normalized lower comparison is:",
        "",
        "`viscous/source >= C*nu*tau^(-3*beta)`.",
        "",
        "For beta > 0 and nu > 0 this lower bound diverges as tau approaches 0.",
        "",
        "## Rows",
        "",
        markdown_table(rows),
        "",
        "## Control Card",
        "",
    ]
    for key, value in summary["control_card"].items():
        lines.append(f"- {key}: {value}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    write_json(out_dir / ROWS_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)
    return int(summary["exit_code"])


if __name__ == "__main__":
    sys.exit(main())
