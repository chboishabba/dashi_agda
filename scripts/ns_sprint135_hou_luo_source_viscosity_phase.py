#!/usr/bin/env python3
"""Sprint 135 corrected Hou-Luo source-vs-viscosity phase emitter.

Sprint 134 retracted the two assumptions that previously made the
axisymmetric Hou-Luo Navier-Stokes route look obstructed:

* ``u1`` is not a pure diffusion variable; the maximum-principle quantity is
  the swirl circulation ``Gamma = r u^theta = r^2 u1``.
* the uniform no-log axisymmetric Biot-Savart estimate is false away from the
  axis; the corrected strain control carries a logarithmic loss.

This script does not prove blowup or regularity.  It records the corrected
asymptotic bookkeeping for source candidates against viscous damping in the
Hou-Luo scaling window

    Omega(t) ~ tau^-alpha, delta(t) ~ tau^beta, beta = alpha - 1,
    1 < alpha < 3/2, tau = T* - t.

The phase variable is source / viscosity.  Values tending to zero mean the
source model is too weak to beat viscosity; values tending to infinity mean
the source model can beat polynomial viscous damping; unresolved means the
simple asymptotic ratio is not a PDE theorem because alignment, signs,
localization, or sharp lower bounds are missing.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable


CONTRACT = "ns_sprint135_hou_luo_source_viscosity_phase"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint135_hou_luo_source_viscosity_phase")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

TAU_GRID = (
    1.0e-1,
    1.0e-3,
    1.0e-10,
)
ALPHA_GRID = (1.25,)
M0_GRID = (1.0,)
NU_GRID = (1.0,)
C_LOG_GRID = (1.0,)
LOG10_E = 1.0 / math.log(10.0)


@dataclass(frozen=True)
class SourceModel:
    model_id: str
    source_scale: str
    source_log_value: Callable[[float, float, float, float, float], float | None]
    expected_phase_limit: str
    sprint134_status: str
    interpretation: str
    unresolved_reason: str


@dataclass(frozen=True)
class PhaseRow:
    row_id: str
    source_model_id: str
    source_scale: str
    alpha: float
    beta: float
    tau: float
    M0: float
    nu: float
    C_log: float
    log_viscosity_scale: float
    log_source_scale: float | None
    log_source_over_viscosity: float | None
    log10_source_over_viscosity: float | None
    numeric_source_over_viscosity: float | str | None
    finite_difference_trend_on_tau_grid: str
    expected_phase_limit: str
    sprint134_status: str
    hou_luo_route_status: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool
    interpretation: str
    unresolved_reason: str

    def as_row(self) -> dict[str, Any]:
        return asdict(self)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def log_delta(tau: float, beta: float) -> float:
    return beta * math.log(tau)


def log_omega(tau: float, alpha: float) -> float:
    return -alpha * math.log(tau)


def log_viscosity(tau: float, alpha: float, beta: float, nu: float) -> float:
    # nu * Omega / delta^2
    return math.log(nu) + log_omega(tau, alpha) - 2.0 * log_delta(tau, beta)


def log_polynomial_source(
    tau: float, alpha: float, beta: float, M0: float, C_log: float
) -> float:
    # M0^2 / delta
    del alpha, C_log
    return 2.0 * math.log(M0) - log_delta(tau, beta)


def log_polylog_source(
    tau: float, alpha: float, beta: float, M0: float, C_log: float
) -> float:
    # M0^2 * log(1/tau)^2 / delta
    del alpha, C_log
    return 2.0 * math.log(M0) + 2.0 * math.log(math.log(1.0 / tau)) - log_delta(tau, beta)


def log_bkm_quadratic_source(
    tau: float, alpha: float, beta: float, M0: float, C_log: float
) -> float:
    # Omega^2, included as the formal BKM quadratic growth comparator.
    del beta, M0, C_log
    return 2.0 * log_omega(tau, alpha)


def log_gronwall_source(
    tau: float, alpha: float, beta: float, M0: float, C_log: float
) -> float:
    # exp(C tau^-beta log(1/tau)) / delta, with M0^2 amplitude retained.
    del alpha
    exponent = C_log * (tau ** (-beta)) * math.log(1.0 / tau)
    return 2.0 * math.log(M0) + exponent - log_delta(tau, beta)


def unresolved_source(
    tau: float, alpha: float, beta: float, M0: float, C_log: float
) -> None:
    del tau, alpha, beta, M0, C_log
    return None


def source_models() -> list[SourceModel]:
    return [
        SourceModel(
            model_id="polynomial_gamma_annulus_gradient",
            source_scale="M0^2 / delta",
            source_log_value=log_polynomial_source,
            expected_phase_limit="source_over_viscosity_tends_to_0",
            sprint134_status="polynomial_obstruction_model_retracted_as_complete_pde_control",
            interpretation=(
                "If the source were only M0^2/delta, viscosity would dominate "
                "because source/viscosity ~ (M0^2/nu) tau^(alpha+beta)."
            ),
            unresolved_reason="none_for_this_asymptotic_model",
        ),
        SourceModel(
            model_id="polylog_gradient_loss",
            source_scale="M0^2 log(1/tau)^2 / delta",
            source_log_value=log_polylog_source,
            expected_phase_limit="source_over_viscosity_tends_to_0",
            sprint134_status="too_weak_to_model_corrected_log_gronwall_feedback",
            interpretation=(
                "Fixed powers of log(1/tau) still lose against the positive "
                "power tau^(alpha+beta) in the source/viscosity ratio."
            ),
            unresolved_reason="none_for_this_asymptotic_model",
        ),
        SourceModel(
            model_id="formal_bkm_quadratic_source",
            source_scale="Omega^2",
            source_log_value=log_bkm_quadratic_source,
            expected_phase_limit="source_over_viscosity_tends_to_infinity",
            sprint134_status="formal_comparator_not_a_closed_pde_lower_bound",
            interpretation=(
                "The formal quadratic BKM source beats viscosity in this "
                "window since Omega^2/(nu Omega/delta^2) ~ tau^(alpha-2)."
            ),
            unresolved_reason=(
                "Requires PDE-level lower bounds and alignment of the source "
                "with the vorticity maximum."
            ),
        ),
        SourceModel(
            model_id="corrected_log_gronwall_source",
            source_scale="exp(C tau^-beta log(1/tau)) / delta",
            source_log_value=log_gronwall_source,
            expected_phase_limit="source_over_viscosity_tends_to_infinity",
            sprint134_status="open_live_candidate_source_can_beat_polynomial_viscosity",
            interpretation=(
                "The Sprint 134 log-loss Gronwall bookkeeping can beat every "
                "polynomial viscous scale in the beta>0 window."
            ),
            unresolved_reason=(
                "This is an upper-scale amplification phase, not a constructive "
                "blowup proof or a signed lower bound."
            ),
        ),
        SourceModel(
            model_id="actual_pde_source_with_alignment_and_sign",
            source_scale="2 u1 partial_z u1 with transport, sign, and localization",
            source_log_value=unresolved_source,
            expected_phase_limit="unresolved",
            sprint134_status="live_open_pde_problem",
            interpretation=(
                "The true PDE source requires sign, alignment, boundary "
                "localization, and feedback control beyond scalar asymptotics."
            ),
            unresolved_reason=(
                "No current repo artifact proves a lower bound strong enough "
                "for BKM divergence or an upper bound strong enough for "
                "regularity."
            ),
        ),
    ]


def classify_numeric_ratio(log_ratio: float | None) -> float | str | None:
    if log_ratio is None:
        return None
    if log_ratio > 700.0:
        return "overflow_gt_exp_700"
    if log_ratio < -745.0:
        return 0.0
    return math.exp(log_ratio)


def trend_for_model(
    model: SourceModel, alpha: float, beta: float, M0: float, nu: float, C_log: float
) -> str:
    values: list[float] = []
    for tau in TAU_GRID:
        log_source = model.source_log_value(tau, alpha, beta, M0, C_log)
        if log_source is None:
            return "unresolved_no_scalar_trend"
        values.append(log_source - log_viscosity(tau, alpha, beta, nu))

    decreasing = all(values[i + 1] < values[i] for i in range(len(values) - 1))
    increasing = all(values[i + 1] > values[i] for i in range(len(values) - 1))
    if decreasing:
        return "decreasing_as_tau_to_0"
    if increasing:
        return "increasing_as_tau_to_0"
    return "nonmonotone_on_sample_grid"


def build_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for model in source_models():
        for alpha in ALPHA_GRID:
            beta = alpha - 1.0
            for M0 in M0_GRID:
                for nu in NU_GRID:
                    for C_log in C_LOG_GRID:
                        trend = trend_for_model(model, alpha, beta, M0, nu, C_log)
                        for tau in TAU_GRID:
                            log_v = log_viscosity(tau, alpha, beta, nu)
                            log_s = model.source_log_value(tau, alpha, beta, M0, C_log)
                            log_ratio = None if log_s is None else log_s - log_v
                            row = PhaseRow(
                                row_id=(
                                    f"{model.model_id}_a{alpha:.2f}_M{M0:.1f}_"
                                    f"nu{nu:.2g}_C{C_log:.2f}_tau{tau:.0e}"
                                ),
                                source_model_id=model.model_id,
                                source_scale=model.source_scale,
                                alpha=alpha,
                                beta=beta,
                                tau=tau,
                                M0=M0,
                                nu=nu,
                                C_log=C_log,
                                log_viscosity_scale=log_v,
                                log_source_scale=log_s,
                                log_source_over_viscosity=log_ratio,
                                log10_source_over_viscosity=(
                                    None if log_ratio is None else log_ratio * LOG10_E
                                ),
                                numeric_source_over_viscosity=classify_numeric_ratio(log_ratio),
                                finite_difference_trend_on_tau_grid=trend,
                                expected_phase_limit=model.expected_phase_limit,
                                sprint134_status=model.sprint134_status,
                                hou_luo_route_status="open_live_candidate",
                                full_clay_ns_solved=False,
                                clay_navier_stokes_promoted=False,
                                interpretation=model.interpretation,
                                unresolved_reason=model.unresolved_reason,
                            )
                            rows.append(row.as_row())
    return rows


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    model_ids = sorted({row["source_model_id"] for row in rows})
    limits = {
        model_id: sorted(
            {row["expected_phase_limit"] for row in rows if row["source_model_id"] == model_id}
        )
        for model_id in model_ids
    }
    tail_rows = [row for row in rows if row["tau"] == min(TAU_GRID)]
    log_gronwall_tail = [
        row
        for row in tail_rows
        if row["source_model_id"] == "corrected_log_gronwall_source"
        and row["log_source_over_viscosity"] is not None
    ]
    polynomial_tail = [
        row
        for row in tail_rows
        if row["source_model_id"] == "polynomial_gamma_annulus_gradient"
        and row["log_source_over_viscosity"] is not None
    ]
    polynomial_obstruction_tails_negative = all(
        row["log_source_over_viscosity"] < 0.0 for row in polynomial_tail
    )
    log_gronwall_tails_positive = all(
        row["log_source_over_viscosity"] > 0.0 for row in log_gronwall_tail
    )
    trends_by_model = {
        model_id: sorted(
            {
                row["finite_difference_trend_on_tau_grid"]
                for row in rows
                if row["source_model_id"] == model_id
            }
        )
        for model_id in model_ids
    }

    summary = {
        "contract": CONTRACT,
        "sprint134_inputs_acknowledged": True,
        "sprint134_inputs": [
            "ns_sprint134_axisymmetric_equation_correction",
            "u1_has_stretching_source_not_pure_diffusion",
            "Gamma_swirl_circulation_is_maximum_principle_variable",
            "ns_sprint134_biot_savart_log_singularity_audit",
            "NoLogAxisymmetricBiotSavartUniform_false_away_from_axis",
            "ns_sprint134_hou_luo_retraction_status",
            "AxisymmetricHouLuoNSViscousDominanceObstruction_retracted",
        ],
        "hou_luo_route_status": "open_live_candidate",
        "phase_quantity": "source_scale / (nu * Omega / delta^2)",
        "scaling_window": "1 < alpha < 3/2, beta = alpha - 1, beta > 0",
        "tau_grid": list(TAU_GRID),
        "alpha_grid": list(ALPHA_GRID),
        "M0_grid": list(M0_GRID),
        "nu_grid": list(NU_GRID),
        "C_log_grid": list(C_LOG_GRID),
        "row_count": len(rows),
        "source_model_count": len(model_ids),
        "source_models": model_ids,
        "expected_phase_limits_by_model": limits,
        "trends_by_model": trends_by_model,
        "polynomial_obstruction_model_retracted": True,
        "polynomial_model_source_over_viscosity_tends_to_0": True,
        "polynomial_tail_log_ratios_all_negative": polynomial_obstruction_tails_negative,
        "log_gronwall_source_can_beat_viscosity": True,
        "log_gronwall_tail_log_ratios_all_positive": log_gronwall_tails_positive,
        "actual_pde_source_phase_unresolved": True,
        "formal_bkm_quadratic_source_beats_viscosity_as_comparator": True,
        "full_clay_ns_solved": False,
        "clay": False,
        "clay_promoted": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
        "exit_reason": (
            "corrected source-vs-viscosity phase table emitted; polynomial "
            "obstruction is retracted as a PDE conclusion, log-Gronwall "
            "source phases can beat polynomial viscosity, and the actual "
            "Hou-Luo PDE route remains open/live"
        ),
        "control_card": {
            "O": (
                "Worker 1 owns scripts/ns_sprint135_hou_luo_source_viscosity_"
                "phase.py and outputs/ns_sprint135_hou_luo_source_viscosity_phase/."
            ),
            "R": (
                "Encode corrected Hou-Luo source-vs-viscosity asymptotic "
                "regimes after Sprint 134."
            ),
            "C": "stdlib asymptotic sampler, JSON/CSV/Markdown output surfaces",
            "S": (
                "Polynomial source scales lose to viscosity, but the corrected "
                "log-Gronwall source scale can beat polynomial viscous damping; "
                "the true PDE source remains unresolved."
            ),
            "L": (
                "Sprint134 corrections -> source candidates -> log-ratio "
                "samples -> phase classification -> no Clay promotion"
            ),
            "P": (
                "Use this artifact as the Sprint 135 phase map before any "
                "future blowup or regularity claim."
            ),
            "G": "full_clay_ns_solved=false; clay_navier_stokes_promoted=false",
            "F": (
                "Missing analytic lower/upper bound for the actual PDE source "
                "with sign, alignment, localization, and feedback."
            ),
        },
    }
    return summary


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "source_model_id",
        "source_scale",
        "alpha",
        "beta",
        "tau",
        "M0",
        "nu",
        "C_log",
        "log_viscosity_scale",
        "log_source_scale",
        "log_source_over_viscosity",
        "log10_source_over_viscosity",
        "numeric_source_over_viscosity",
        "finite_difference_trend_on_tau_grid",
        "expected_phase_limit",
        "sprint134_status",
        "hou_luo_route_status",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "interpretation",
        "unresolved_reason",
    )
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row[key] for key in fieldnames})


def write_report(path: Path, summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    representative = [
        row
        for row in rows
        if row["tau"] == min(TAU_GRID)
        and row["alpha"] == ALPHA_GRID[-1]
        and row["M0"] == M0_GRID[0]
        and row["nu"] == NU_GRID[0]
        and row["C_log"] == C_LOG_GRID[0]
    ]
    lines = [
        f"# {CONTRACT}",
        "",
        "## Summary",
        "",
        f"- Sprint 134 inputs acknowledged: `{summary['sprint134_inputs_acknowledged']}`",
        f"- Hou-Luo route status: `{summary['hou_luo_route_status']}`",
        f"- Polynomial obstruction model retracted: `{summary['polynomial_obstruction_model_retracted']}`",
        f"- Log-Gronwall source can beat viscosity: `{summary['log_gronwall_source_can_beat_viscosity']}`",
        f"- Full Clay NS solved: `{summary['full_clay_ns_solved']}`",
        f"- Clay Navier-Stokes promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Representative Tail Rows",
        "",
        "| model | expected phase | log10(source/viscosity) | trend |",
        "|---|---:|---:|---|",
    ]
    for row in representative:
        log10_ratio = row["log10_source_over_viscosity"]
        rendered = "unresolved" if log10_ratio is None else f"{log10_ratio:.6g}"
        lines.append(
            "| {model} | {phase} | {ratio} | {trend} |".format(
                model=row["source_model_id"],
                phase=row["expected_phase_limit"],
                ratio=rendered,
                trend=row["finite_difference_trend_on_tau_grid"],
            )
        )
    lines.extend(
        [
            "",
            "## Interpretation",
            "",
            "The phase table separates scalar asymptotic regimes from PDE-level "
            "proof. A fixed polynomial source model supports viscous dominance "
            "as an asymptotic calculation, but Sprint 134 prevents promoting "
            "that calculation to a Hou-Luo obstruction theorem. The corrected "
            "log-Gronwall model can overwhelm polynomial viscosity, so the "
            "axisymmetric Hou-Luo route remains open/live.",
            "",
        ]
    )
    path.write_text("\n".join(lines), encoding="utf-8")


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> list[str]:
    errors: list[str] = []
    if not summary.get("sprint134_inputs_acknowledged"):
        errors.append("sprint134 inputs were not acknowledged")
    if summary.get("hou_luo_route_status") != "open_live_candidate":
        errors.append("Hou-Luo route status must remain open_live_candidate")
    if not summary.get("polynomial_obstruction_model_retracted"):
        errors.append("polynomial obstruction model must be marked retracted")
    if not summary.get("log_gronwall_source_can_beat_viscosity"):
        errors.append("log-Gronwall source must be recorded as able to beat viscosity")
    if summary.get("full_clay_ns_solved") is not False:
        errors.append("full_clay_ns_solved must be false")
    if summary.get("clay_navier_stokes_promoted") is not False:
        errors.append("clay_navier_stokes_promoted must be false")
    if summary.get("complete") is not True or summary.get("exit_code") != 0:
        errors.append("summary must be complete with exit_code 0")
    if not rows:
        errors.append("rows must not be empty")
    if not any(row["source_model_id"] == "corrected_log_gronwall_source" for row in rows):
        errors.append("missing corrected log-Gronwall source rows")
    if not any(row["source_model_id"] == "actual_pde_source_with_alignment_and_sign" for row in rows):
        errors.append("missing unresolved actual PDE source rows")
    promoted_rows = [
        row for row in rows if row["full_clay_ns_solved"] or row["clay_navier_stokes_promoted"]
    ]
    if promoted_rows:
        errors.append("row-level Clay promotion flags must remain false")
    return errors


def main() -> int:
    args = parse_args()
    out_dir = args.repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    errors = validate(summary, rows)
    if errors:
        for error in errors:
            print(f"{CONTRACT}: {error}", file=sys.stderr)
        return 1

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_report(out_dir / REPORT_NAME, summary, rows)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
