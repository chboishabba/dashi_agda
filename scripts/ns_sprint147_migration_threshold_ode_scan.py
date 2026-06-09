#!/usr/bin/env python3
"""Sprint 147 migration-threshold ODE scan.

This deterministic stdlib artifact explores a transparent reduced ODE model
for migration initiation in the Hou-Luo-inspired Navier-Stokes evidence lane.
It is evidence only.  It models four scalar toy quantities:

* P(t): plane baseline source amplitude, decaying under viscosity and leakage;
* A(t): off-axis source amplitude, fed by P and log feedback and damped by
  viscosity;
* L(t): logarithmic feedback state, driven by off-axis/plane contrast; and
* S(t): accumulated suppression index from viscous damping.

Migration is classified when A/(P+eps) and A both cross fixed thresholds before
suppression.  Suppression is classified when S crosses a threshold or P decays
below its floor before migration.  The scan names several parameter regimes and
small deterministic perturbation cases.

The output is not a PDE proof, not a blowup proof, and not a Clay promotion.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import sys
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Callable


CONTRACT = "ns_sprint147_migration_threshold_ode_scan"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint147_migration_threshold_ode_scan")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

SPRINT = 147
LANE = 3
PROGRAM = "HouLuoAxisymmetricWithSwirlBarrierProgram"
GATE = "MigrationInitiationThresholdReducedODEScan"
MODEL_KIND = "deterministic_transparent_reduced_ode_evidence_only"
ROUTE_DECISION = "evidence_some_regimes_initiate_migration_before_suppression"
PROMOTION_DECISION = "hold_no_clay_promotion"

MIGRATION_RATIO_THRESHOLD = 0.72
OFF_AXIS_ABS_THRESHOLD = 0.14
SUPPRESSION_THRESHOLD = 1.0
PLANE_FLOOR = 0.07
EPS = 1.0e-9
T0 = 0.0
T_END = 24.0
DT = 0.01


@dataclass(frozen=True)
class Regime:
    regime_id: str
    regime_name: str
    description: str
    p0: float
    a0: float
    l0: float
    s0: float
    nu: float
    plane_decay: float
    plane_leak_to_offaxis: float
    offaxis_source_gain: float
    offaxis_viscous_weight: float
    offaxis_nonlinear_suppression: float
    log_feedback_gain: float
    log_drive: float
    log_relax: float
    log_saturation: float
    suppression_weight: float
    suppression_log_weight: float
    k_plane: float = 1.0
    k_offaxis: float = 1.35


@dataclass(frozen=True)
class ScanVariant:
    variant_id: str
    source_multiplier: float
    log_multiplier: float
    viscosity_multiplier: float
    description: str


@dataclass(frozen=True)
class State:
    p: float
    a: float
    l: float
    s: float


@dataclass(frozen=True)
class Event:
    event: str
    t: float
    reason: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    parser.add_argument("--t-end", type=float, default=T_END)
    parser.add_argument("--dt", type=float, default=DT)
    return parser.parse_args()


def stable_hash(value: Any) -> str:
    encoded = json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def clamp_nonnegative(value: float) -> float:
    if value < 0.0:
        return 0.0
    if value > 1.0e6:
        return 1.0e6
    return value


def model_rhs(regime: Regime, state: State) -> State:
    p = max(state.p, 0.0)
    a = max(state.a, 0.0)
    l = max(state.l, 0.0)
    s = max(state.s, 0.0)
    log_factor = math.log1p(l)
    contrast = a / (p + EPS)

    dp = (
        -regime.nu * regime.k_plane * regime.k_plane * regime.plane_decay * p
        - regime.plane_leak_to_offaxis * p * a
    )
    da = (
        regime.offaxis_source_gain * p * (1.0 + regime.log_feedback_gain * log_factor)
        + 0.18 * regime.plane_leak_to_offaxis * p * a
        - regime.nu
        * regime.k_offaxis
        * regime.k_offaxis
        * regime.offaxis_viscous_weight
        * a
        - regime.offaxis_nonlinear_suppression * a * a
        - 0.08 * s * a
    )
    dl = (
        regime.log_drive * contrast
        - regime.log_relax * l
        - regime.log_saturation * l * l
    )
    ds = (
        regime.suppression_weight * regime.nu * (p + 0.65 * a)
        + regime.suppression_log_weight * regime.nu * log_factor
    )
    return State(dp, da, dl, ds)


def add_state(x: State, y: State, scale: float) -> State:
    return State(
        x.p + scale * y.p,
        x.a + scale * y.a,
        x.l + scale * y.l,
        x.s + scale * y.s,
    )


def rk4_step(regime: Regime, state: State, dt: float) -> State:
    k1 = model_rhs(regime, state)
    k2 = model_rhs(regime, add_state(state, k1, 0.5 * dt))
    k3 = model_rhs(regime, add_state(state, k2, 0.5 * dt))
    k4 = model_rhs(regime, add_state(state, k3, dt))
    return State(
        clamp_nonnegative(state.p + (dt / 6.0) * (k1.p + 2.0 * k2.p + 2.0 * k3.p + k4.p)),
        clamp_nonnegative(state.a + (dt / 6.0) * (k1.a + 2.0 * k2.a + 2.0 * k3.a + k4.a)),
        clamp_nonnegative(state.l + (dt / 6.0) * (k1.l + 2.0 * k2.l + 2.0 * k3.l + k4.l)),
        clamp_nonnegative(state.s + (dt / 6.0) * (k1.s + 2.0 * k2.s + 2.0 * k3.s + k4.s)),
    )


def migration_trigger(state: State) -> bool:
    return (
        state.a / (state.p + EPS) >= MIGRATION_RATIO_THRESHOLD
        and state.a >= OFF_AXIS_ABS_THRESHOLD
    )


def suppression_trigger(state: State) -> tuple[bool, str]:
    if state.s >= SUPPRESSION_THRESHOLD:
        return True, "suppression_index_threshold"
    if state.p <= PLANE_FLOOR:
        return True, "plane_floor_before_migration"
    return False, ""


def first_event(state: State, t: float) -> Event | None:
    if migration_trigger(state):
        return Event("migration_initiated", t, "offaxis_ratio_and_absolute_threshold")
    suppressed, reason = suppression_trigger(state)
    if suppressed:
        return Event("suppressed", t, reason)
    return None


def simulate(regime: Regime, t_end: float, dt: float) -> dict[str, Any]:
    state = State(regime.p0, regime.a0, regime.l0, regime.s0)
    event = first_event(state, T0)
    t = T0
    steps = 0
    max_ratio = state.a / (state.p + EPS)
    max_offaxis = state.a
    min_plane = state.p
    max_log = state.l
    max_suppression = state.s
    ratio_at_migration = None

    while event is None and t < t_end - 0.5 * dt:
        state = rk4_step(regime, state, dt)
        t = round(t + dt, 12)
        steps += 1
        ratio = state.a / (state.p + EPS)
        max_ratio = max(max_ratio, ratio)
        max_offaxis = max(max_offaxis, state.a)
        min_plane = min(min_plane, state.p)
        max_log = max(max_log, state.l)
        max_suppression = max(max_suppression, state.s)
        event = first_event(state, t)
        if event is not None and event.event == "migration_initiated":
            ratio_at_migration = ratio

    if event is None:
        event = Event("no_event_by_horizon", t_end, "neither_threshold_crossed")

    final_ratio = state.a / (state.p + EPS)
    if ratio_at_migration is None and event.event == "migration_initiated":
        ratio_at_migration = final_ratio

    return {
        "event": event.event,
        "event_time": round(event.t, 6),
        "event_reason": event.reason,
        "steps": steps,
        "final_p": round(state.p, 10),
        "final_a": round(state.a, 10),
        "final_l": round(state.l, 10),
        "final_s": round(state.s, 10),
        "final_ratio": round(final_ratio, 10),
        "max_ratio": round(max_ratio, 10),
        "max_offaxis": round(max_offaxis, 10),
        "min_plane": round(min_plane, 10),
        "max_log": round(max_log, 10),
        "max_suppression": round(max_suppression, 10),
        "ratio_at_migration": None if ratio_at_migration is None else round(ratio_at_migration, 10),
        "migration_before_suppression": event.event == "migration_initiated",
    }


def base_regimes() -> list[Regime]:
    return [
        Regime(
            regime_id="plane_baseline_viscous_suppression",
            regime_name="Plane baseline viscous suppression",
            description="Plane source decays and viscosity accumulates before off-axis gain can cross the threshold.",
            p0=1.0,
            a0=0.025,
            l0=0.04,
            s0=0.0,
            nu=0.17,
            plane_decay=1.05,
            plane_leak_to_offaxis=0.03,
            offaxis_source_gain=0.045,
            offaxis_viscous_weight=1.15,
            offaxis_nonlinear_suppression=0.26,
            log_feedback_gain=0.35,
            log_drive=0.10,
            log_relax=0.23,
            log_saturation=0.035,
            suppression_weight=0.72,
            suppression_log_weight=0.10,
        ),
        Regime(
            regime_id="balanced_threshold_competition",
            regime_name="Balanced threshold competition",
            description="Source gain and viscosity are close enough that threshold ordering is parameter-sensitive.",
            p0=1.0,
            a0=0.035,
            l0=0.08,
            s0=0.0,
            nu=0.105,
            plane_decay=0.78,
            plane_leak_to_offaxis=0.08,
            offaxis_source_gain=0.075,
            offaxis_viscous_weight=0.88,
            offaxis_nonlinear_suppression=0.18,
            log_feedback_gain=0.68,
            log_drive=0.20,
            log_relax=0.17,
            log_saturation=0.026,
            suppression_weight=0.55,
            suppression_log_weight=0.07,
        ),
        Regime(
            regime_id="offaxis_source_favorable",
            regime_name="Off-axis source favorable",
            description="Off-axis gain is deliberately strong enough to initiate migration before suppression in the toy model.",
            p0=1.0,
            a0=0.05,
            l0=0.10,
            s0=0.0,
            nu=0.075,
            plane_decay=0.62,
            plane_leak_to_offaxis=0.13,
            offaxis_source_gain=0.125,
            offaxis_viscous_weight=0.70,
            offaxis_nonlinear_suppression=0.12,
            log_feedback_gain=0.82,
            log_drive=0.30,
            log_relax=0.13,
            log_saturation=0.020,
            suppression_weight=0.40,
            suppression_log_weight=0.05,
        ),
        Regime(
            regime_id="log_feedback_favorable",
            regime_name="Log feedback favorable",
            description="Moderate source gain is amplified by a persistent logarithmic feedback variable.",
            p0=1.0,
            a0=0.04,
            l0=0.32,
            s0=0.0,
            nu=0.080,
            plane_decay=0.70,
            plane_leak_to_offaxis=0.07,
            offaxis_source_gain=0.088,
            offaxis_viscous_weight=0.76,
            offaxis_nonlinear_suppression=0.11,
            log_feedback_gain=1.28,
            log_drive=0.42,
            log_relax=0.09,
            log_saturation=0.020,
            suppression_weight=0.42,
            suppression_log_weight=0.045,
        ),
        Regime(
            regime_id="high_viscosity_suppressed",
            regime_name="High viscosity suppressed",
            description="High viscosity and high off-axis damping suppress migration in the reduced system.",
            p0=1.0,
            a0=0.03,
            l0=0.06,
            s0=0.0,
            nu=0.28,
            plane_decay=1.15,
            plane_leak_to_offaxis=0.04,
            offaxis_source_gain=0.065,
            offaxis_viscous_weight=1.45,
            offaxis_nonlinear_suppression=0.28,
            log_feedback_gain=0.42,
            log_drive=0.14,
            log_relax=0.25,
            log_saturation=0.04,
            suppression_weight=0.85,
            suppression_log_weight=0.12,
        ),
        Regime(
            regime_id="weak_feedback_no_migration",
            regime_name="Weak feedback no migration",
            description="Off-axis source exists, but weak log feedback keeps the migration ratio below threshold.",
            p0=1.0,
            a0=0.032,
            l0=0.02,
            s0=0.0,
            nu=0.12,
            plane_decay=0.90,
            plane_leak_to_offaxis=0.045,
            offaxis_source_gain=0.055,
            offaxis_viscous_weight=0.92,
            offaxis_nonlinear_suppression=0.22,
            log_feedback_gain=0.08,
            log_drive=0.05,
            log_relax=0.30,
            log_saturation=0.05,
            suppression_weight=0.62,
            suppression_log_weight=0.055,
        ),
    ]


def scan_variants() -> list[ScanVariant]:
    return [
        ScanVariant("nominal", 1.0, 1.0, 1.0, "Named regime as specified."),
        ScanVariant("source_low", 0.82, 1.0, 1.0, "Reduced off-axis source gain."),
        ScanVariant("source_high", 1.18, 1.0, 1.0, "Increased off-axis source gain."),
        ScanVariant("log_low", 1.0, 0.78, 1.0, "Reduced log drive and feedback."),
        ScanVariant("log_high", 1.0, 1.24, 1.0, "Increased log drive and feedback."),
        ScanVariant("viscosity_low", 1.0, 1.0, 0.82, "Reduced viscosity damping."),
        ScanVariant("viscosity_high", 1.0, 1.0, 1.20, "Increased viscosity damping."),
    ]


def apply_variant(regime: Regime, variant: ScanVariant) -> Regime:
    return replace(
        regime,
        nu=regime.nu * variant.viscosity_multiplier,
        offaxis_source_gain=regime.offaxis_source_gain * variant.source_multiplier,
        log_feedback_gain=regime.log_feedback_gain * variant.log_multiplier,
        log_drive=regime.log_drive * variant.log_multiplier,
    )


def build_rows(t_end: float, dt: float) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for regime in base_regimes():
        for variant in scan_variants():
            varied = apply_variant(regime, variant)
            result = simulate(varied, t_end=t_end, dt=dt)
            row: dict[str, Any] = {
                "row_id": f"{regime.regime_id}::{variant.variant_id}",
                "regime_id": regime.regime_id,
                "regime_name": regime.regime_name,
                "regime_description": regime.description,
                "variant_id": variant.variant_id,
                "variant_description": variant.description,
                "source_multiplier": variant.source_multiplier,
                "log_multiplier": variant.log_multiplier,
                "viscosity_multiplier": variant.viscosity_multiplier,
                "model_kind": MODEL_KIND,
                "p0": varied.p0,
                "a0": varied.a0,
                "l0": varied.l0,
                "s0": varied.s0,
                "nu": round(varied.nu, 10),
                "plane_decay": varied.plane_decay,
                "plane_leak_to_offaxis": varied.plane_leak_to_offaxis,
                "offaxis_source_gain": round(varied.offaxis_source_gain, 10),
                "offaxis_viscous_weight": varied.offaxis_viscous_weight,
                "offaxis_nonlinear_suppression": varied.offaxis_nonlinear_suppression,
                "log_feedback_gain": round(varied.log_feedback_gain, 10),
                "log_drive": round(varied.log_drive, 10),
                "log_relax": varied.log_relax,
                "log_saturation": varied.log_saturation,
                "suppression_weight": varied.suppression_weight,
                "suppression_log_weight": varied.suppression_log_weight,
                "migration_ratio_threshold": MIGRATION_RATIO_THRESHOLD,
                "off_axis_abs_threshold": OFF_AXIS_ABS_THRESHOLD,
                "suppression_threshold": SUPPRESSION_THRESHOLD,
                "plane_floor": PLANE_FLOOR,
                "t_end": t_end,
                "dt": dt,
                **result,
                "evidence_role": "toy_ode_parameter_scan_not_proof",
                "theorem_proved": False,
                "blowup_existence_proved": False,
                "full_clay_ns_solved": False,
                "clay_navier_stokes_promoted": False,
            }
            row["row_hash"] = stable_hash({k: v for k, v in row.items() if k != "row_hash"})
            rows.append(row)
    rows.sort(key=lambda item: item["row_id"])
    return rows


def write_json(path: Path, payload: Any) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    fieldnames = (
        "row_id",
        "regime_id",
        "regime_name",
        "variant_id",
        "source_multiplier",
        "log_multiplier",
        "viscosity_multiplier",
        "event",
        "event_time",
        "event_reason",
        "migration_before_suppression",
        "max_ratio",
        "max_offaxis",
        "min_plane",
        "max_log",
        "max_suppression",
        "final_p",
        "final_a",
        "final_l",
        "final_s",
        "final_ratio",
        "ratio_at_migration",
        "nu",
        "offaxis_source_gain",
        "log_feedback_gain",
        "log_drive",
        "t_end",
        "dt",
        "evidence_role",
        "theorem_proved",
        "blowup_existence_proved",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "row_hash",
    )
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row[key] for key in fieldnames})


def regime_counts(rows: list[dict[str, Any]], predicate: Callable[[dict[str, Any]], bool]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        if predicate(row):
            counts[row["regime_id"]] = counts.get(row["regime_id"], 0) + 1
    return dict(sorted(counts.items()))


def build_control_card() -> dict[str, str]:
    return {
        "O": (
            "Sprint 147 lane 3 owns only "
            "scripts/ns_sprint147_migration_threshold_ode_scan.py and "
            "outputs/ns_sprint147_migration_threshold_ode_scan/."
        ),
        "R": (
            "Emit a deterministic reduced ODE/parameter scan for the migration "
            "initiation threshold, with explicit fail-closed proof guards."
        ),
        "C": (
            "Four-variable toy ODE: P plane baseline decay, A off-axis source "
            "gain/damping, L logarithmic feedback, S accumulated suppression."
        ),
        "S": (
            "Named regimes are scanned under nominal, source, log, and "
            "viscosity perturbation variants using fixed-step RK4."
        ),
        "L": (
            "Rows classify first threshold ordering only; migration before "
            "suppression is numerical evidence in this reduced model, not a "
            "Navier-Stokes theorem."
        ),
        "P": (
            "Use positive rows to prioritize analytic migration-threshold "
            "obligations and negative rows to identify damping-dominated "
            "toy regimes."
        ),
        "G": (
            "Validation requires some deterministic rows, stable hashes, hard "
            "false theorem/proof/Clay guards, and at least one migrated regime "
            "before setting ode_scan_supports_some_regimes."
        ),
        "F": (
            "Any accidental theorem proof, blowup proof, full Clay solution, "
            "Clay promotion, missing row hashes, or non-positive dt fails the "
            "artifact."
        ),
    }


def build_summary(rows: list[dict[str, Any]], t_end: float, dt: float) -> dict[str, Any]:
    migrated = [row for row in rows if row["migration_before_suppression"]]
    suppressed = [row for row in rows if row["event"] == "suppressed"]
    no_event = [row for row in rows if row["event"] == "no_event_by_horizon"]
    row_hashes = {row["row_id"]: row["row_hash"] for row in rows}
    rows_hash = stable_hash(rows)
    ode_scan_supports_some_regimes = bool(migrated)

    invariant_failures: list[str] = []
    if dt <= 0.0:
        invariant_failures.append("non_positive_dt")
    if t_end <= T0:
        invariant_failures.append("non_positive_time_horizon")
    if not rows:
        invariant_failures.append("no_rows")
    if any(not row.get("row_hash") for row in rows):
        invariant_failures.append("missing_row_hash")
    for guard in (
        "theorem_proved",
        "blowup_existence_proved",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    ):
        if any(row[guard] for row in rows):
            invariant_failures.append(f"{guard}_row_true")
    if ode_scan_supports_some_regimes and not migrated:
        invariant_failures.append("support_flag_without_migrated_rows")
    if not ode_scan_supports_some_regimes and migrated:
        invariant_failures.append("migrated_rows_without_support_flag")

    invariants_passed = not invariant_failures
    return {
        "contract": CONTRACT,
        "sprint": SPRINT,
        "lane": LANE,
        "program": PROGRAM,
        "gate": GATE,
        "model_kind": MODEL_KIND,
        "route_decision": ROUTE_DECISION if ode_scan_supports_some_regimes else "evidence_no_scanned_regime_initiated_migration",
        "promotion_decision": PROMOTION_DECISION,
        "ode_system": {
            "P": "P' = -nu*k_plane^2*plane_decay*P - plane_leak_to_offaxis*P*A",
            "A": (
                "A' = offaxis_source_gain*P*(1 + log_feedback_gain*log1p(L)) "
                "+ 0.18*plane_leak_to_offaxis*P*A "
                "- nu*k_offaxis^2*offaxis_viscous_weight*A "
                "- offaxis_nonlinear_suppression*A^2 - 0.08*S*A"
            ),
            "L": "L' = log_drive*A/(P+eps) - log_relax*L - log_saturation*L^2",
            "S": "S' = suppression_weight*nu*(P + 0.65*A) + suppression_log_weight*nu*log1p(L)",
        },
        "thresholds": {
            "migration_ratio_threshold": MIGRATION_RATIO_THRESHOLD,
            "off_axis_abs_threshold": OFF_AXIS_ABS_THRESHOLD,
            "suppression_threshold": SUPPRESSION_THRESHOLD,
            "plane_floor": PLANE_FLOOR,
            "eps": EPS,
        },
        "integrator": {
            "method": "fixed_step_rk4",
            "t0": T0,
            "t_end": t_end,
            "dt": dt,
        },
        "row_count": len(rows),
        "regime_count": len({row["regime_id"] for row in rows}),
        "variant_count": len({row["variant_id"] for row in rows}),
        "migration_before_suppression_count": len(migrated),
        "suppressed_count": len(suppressed),
        "no_event_by_horizon_count": len(no_event),
        "migration_before_suppression_by_regime": regime_counts(rows, lambda row: row["migration_before_suppression"]),
        "suppressed_by_regime": regime_counts(rows, lambda row: row["event"] == "suppressed"),
        "no_event_by_regime": regime_counts(rows, lambda row: row["event"] == "no_event_by_horizon"),
        "migrated_row_ids": [row["row_id"] for row in migrated],
        "suppressed_row_ids": [row["row_id"] for row in suppressed],
        "ode_scan_supports_some_regimes": ode_scan_supports_some_regimes,
        "evidence_only": True,
        "theorem_proved": False,
        "blowup_existence_proved": False,
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "claim_closed": False,
        "claim_proved": False,
        "claim_proven": False,
        "proof_claimed": False,
        "promotion_allowed": False,
        "row_hashes": row_hashes,
        "rows_hash": rows_hash,
        "summary_payload_hash_without_self": stable_hash(
            {
                "contract": CONTRACT,
                "row_hashes": row_hashes,
                "rows_hash": rows_hash,
                "thresholds": {
                    "migration_ratio_threshold": MIGRATION_RATIO_THRESHOLD,
                    "off_axis_abs_threshold": OFF_AXIS_ABS_THRESHOLD,
                    "suppression_threshold": SUPPRESSION_THRESHOLD,
                    "plane_floor": PLANE_FLOOR,
                },
            }
        ),
        "control_card": build_control_card(),
        "invariant_failures": invariant_failures,
        "invariants_passed": invariants_passed,
        "exit_code": 0 if invariants_passed else 1,
    }


def validate(summary: dict[str, Any], rows: list[dict[str, Any]]) -> None:
    if summary["contract"] != CONTRACT:
        raise ValueError("wrong contract")
    if summary["model_kind"] != MODEL_KIND:
        raise ValueError("wrong model kind")
    if not rows:
        raise ValueError("scan emitted no rows")
    if not summary["invariants_passed"]:
        raise ValueError("invariants failed: " + ", ".join(summary["invariant_failures"]))
    if summary["theorem_proved"]:
        raise ValueError("theorem_proved must be false")
    if summary["blowup_existence_proved"]:
        raise ValueError("blowup_existence_proved must be false")
    if summary["full_clay_ns_solved"]:
        raise ValueError("full_clay_ns_solved must be false")
    if summary["clay_navier_stokes_promoted"]:
        raise ValueError("clay_navier_stokes_promoted must be false")
    if summary["ode_scan_supports_some_regimes"] != any(row["migration_before_suppression"] for row in rows):
        raise ValueError("ode_scan_supports_some_regimes does not match row data")
    for row in rows:
        if row["event"] == "migration_initiated" and not row["migration_before_suppression"]:
            raise ValueError("migration event row not marked migrated")
        if row["migration_before_suppression"] and row["event"] != "migration_initiated":
            raise ValueError("migrated row has wrong event")
        for guard in (
            "theorem_proved",
            "blowup_existence_proved",
            "full_clay_ns_solved",
            "clay_navier_stokes_promoted",
        ):
            if row[guard]:
                raise ValueError(f"{guard} must be false on every row")


def markdown_table(rows: list[dict[str, Any]]) -> str:
    selected = [
        row
        for row in rows
        if row["variant_id"] == "nominal" or row["migration_before_suppression"]
    ]
    lines = [
        "| Regime | Variant | Event | t | Max A/P | Max A | Guard |",
        "|---|---:|---|---:|---:|---:|---|",
    ]
    for row in selected:
        guard = "migration before suppression" if row["migration_before_suppression"] else "suppressed/no event"
        lines.append(
            "| {regime} | {variant} | {event} | {time:.2f} | {ratio:.3f} | {offaxis:.3f} | {guard} |".format(
                regime=row["regime_name"],
                variant=row["variant_id"],
                event=row["event"],
                time=row["event_time"],
                ratio=row["max_ratio"],
                offaxis=row["max_offaxis"],
                guard=guard,
            )
        )
    return "\n".join(lines)


def build_report(summary: dict[str, Any], rows: list[dict[str, Any]]) -> str:
    control = summary["control_card"]
    migrated_count = summary["migration_before_suppression_count"]
    return "\n".join(
        [
            f"# {CONTRACT}",
            "",
            "## Status",
            "",
            (
                f"Deterministic reduced ODE evidence scan. "
                f"{migrated_count} of {summary['row_count']} scanned rows initiate migration before suppression."
            ),
            "",
            "This artifact is evidence only. It does not prove a theorem, does not prove blowup existence, does not solve full Clay Navier-Stokes, and does not promote a Clay claim.",
            "",
            "## ODE Model",
            "",
            "* P: plane baseline source amplitude.",
            "* A: off-axis source amplitude.",
            "* L: logarithmic feedback state.",
            "* S: accumulated suppression index.",
            "",
            "Migration is initiated when both `A/(P+eps)` and `A` cross their thresholds before suppression. Suppression is triggered by the accumulated suppression index or by plane baseline decay below the configured floor.",
            "",
            "## Guards",
            "",
            f"* `ode_scan_supports_some_regimes`: `{str(summary['ode_scan_supports_some_regimes']).lower()}`",
            "* `theorem_proved`: `false`",
            "* `blowup_existence_proved`: `false`",
            "* `full_clay_ns_solved`: `false`",
            "* `clay_navier_stokes_promoted`: `false`",
            "",
            "## Scan Snapshot",
            "",
            markdown_table(rows),
            "",
            "## O/R/C/S/L/P/G/F",
            "",
            f"* O: {control['O']}",
            f"* R: {control['R']}",
            f"* C: {control['C']}",
            f"* S: {control['S']}",
            f"* L: {control['L']}",
            f"* P: {control['P']}",
            f"* G: {control['G']}",
            f"* F: {control['F']}",
            "",
            "## Hashes",
            "",
            f"* `rows_hash`: `{summary['rows_hash']}`",
            f"* `summary_payload_hash_without_self`: `{summary['summary_payload_hash_without_self']}`",
            "",
        ]
    )


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows(t_end=args.t_end, dt=args.dt)
    summary = build_summary(rows, t_end=args.t_end, dt=args.dt)
    validate(summary, rows)

    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_json(out_dir / SUMMARY_NAME, summary)
    (out_dir / REPORT_NAME).write_text(build_report(summary, rows), encoding="utf-8")

    try:
        out_dir_display = str(out_dir.relative_to(repo_root))
    except ValueError:
        out_dir_display = str(out_dir)

    print(
        json.dumps(
            {
                "contract": CONTRACT,
                "out_dir": out_dir_display,
                "row_count": summary["row_count"],
                "migration_before_suppression_count": summary["migration_before_suppression_count"],
                "ode_scan_supports_some_regimes": summary["ode_scan_supports_some_regimes"],
                "theorem_proved": summary["theorem_proved"],
                "blowup_existence_proved": summary["blowup_existence_proved"],
                "full_clay_ns_solved": summary["full_clay_ns_solved"],
                "clay_navier_stokes_promoted": summary["clay_navier_stokes_promoted"],
                "invariants_passed": summary["invariants_passed"],
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
