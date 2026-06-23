#!/usr/bin/env python3
"""Summarize corrected radial fork follow-up scans.

This is a fail-closed postprocess over the corrected constrained optimizer.
It does not recompute K_N(A). It sweeps candidate thresholds over the retained
profile rows, isolates high-radial/low-dissipation low-frame examples, and
records whether existing Schur and residence surfaces provide usable support.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_triad_radial_fork_followup_summary.py"
CONTRACT = "ns_triad_radial_fork_followup_summary"
ROUTE_DECISION = "FAIL_CLOSED_NS_TRIAD_RADIAL_FORK_FOLLOWUP_SUMMARY"
SCHEMA_VERSION = "1.0.0"

OK_STATUS = "ok"
PARTIAL_STATUS = "partial"
ERROR_STATUS = "error"

DEFAULT_OPTIMIZER_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_constrained_adversarial_fork_optimizer_N128_20260623_large_full.json"
)
DEFAULT_SCHUR_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_schur_directional_audit_scan_N128_20260622.json"
)
DEFAULT_RESIDENCE_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_entropy_residence_summary_20260621.json"
)
DEFAULT_OUTPUT_JSON = Path(
    "scripts/data/outputs/ns_boundary_pressure_geometric_20260621/"
    "ns_triad_radial_fork_followup_summary_N128_20260623.json"
)

AUTHORITY = {
    "candidate_only": True,
    "empirical_non_promoting": True,
    "truth_authority": False,
    "theorem_authority": False,
    "clay_authority": False,
    "runtime_authority": False,
    "promoted": False,
}

CONTROL_CARD = {
    "O": "Postprocess the corrected radial no-triple-danger fork evidence.",
    "R": (
        "Sweep radial thresholds over retained optimizer profiles, isolate high-radial low-D rows, "
        "and condition Schur/residence support on the corrected radial variables."
    ),
    "C": SCRIPT_NAME,
    "S": "Fail-closed telemetry summary; any unresolved-danger row keeps the theorem open.",
    "L": (
        "optimizer profile rows -> threshold grid -> high-radial low-D counterexample search -> "
        "Schur availability -> radial residence pressure summary."
    ),
    "P": ROUTE_DECISION,
    "G": "No theorem, full-NS, or Clay promotion is inferred.",
    "F": "If low-frame/high-radial/low-D rows exist, the corrected fork still needs a sharper variable or proof.",
}


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--optimizer-json", type=Path, default=DEFAULT_OPTIMIZER_JSON)
    parser.add_argument("--schur-json", type=Path, default=DEFAULT_SCHUR_JSON)
    parser.add_argument("--residence-json", type=Path, default=DEFAULT_RESIDENCE_JSON)
    parser.add_argument("--output-json", type=Path, default=DEFAULT_OUTPUT_JSON)
    parser.add_argument("--pretty", action="store_true")
    return parser.parse_args()


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _read_json(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path}: payload must be an object")
    return payload


def _finite(value: Any) -> float | None:
    if value is None or isinstance(value, bool):
        return None
    try:
        parsed = float(value)
    except (TypeError, ValueError):
        return None
    return parsed if math.isfinite(parsed) else None


def _profiles(optimizer: dict[str, Any]) -> list[dict[str, Any]]:
    profiles: list[dict[str, Any]] = []
    for row in optimizer.get("rows", []):
        if not isinstance(row, dict):
            continue
        shell = row.get("shell")
        for profile in row.get("profile_samples", []):
            if not isinstance(profile, dict):
                continue
            item = dict(profile)
            item["shell"] = shell
            profiles.append(item)
    return profiles


def _is_low_frame(profile: dict[str, Any], c0: float) -> bool:
    lmin = _finite(profile.get("lambda_min_kn_a"))
    return lmin is not None and lmin < c0


def _is_high_radial(profile: dict[str, Any], r0: float, eta: float) -> bool:
    radial = _finite(profile.get("radial_effective_scale"))
    high_mass = _finite(profile.get("high_shell_mass_fraction"))
    return (radial is not None and radial >= r0) or (high_mass is not None and high_mass >= eta)


def _is_low_d(profile: dict[str, Any], d0: float) -> bool:
    dissipation = _finite(profile.get("dissipation_proxy"))
    return dissipation is not None and dissipation <= d0


def _threshold_sweep(profiles: list[dict[str, Any]], c0: float) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for r0 in (1.25, 1.5, 1.75, 2.0, 2.5, 3.0):
        for eta in (0.10, 0.15, 0.25, 0.40, 0.60, 0.80):
            for d0 in (1.5, 2.0, 2.5, 3.0, 4.0, 6.0):
                danger = [
                    profile
                    for profile in profiles
                    if _is_low_frame(profile, c0)
                    and _is_high_radial(profile, r0, eta)
                    and _is_low_d(profile, d0)
                ]
                best = min(danger, key=lambda p: float(p["lambda_min_kn_a"])) if danger else None
                rows.append(
                    {
                        "c0": float(c0),
                        "r0": float(r0),
                        "high_shell_eta": float(eta),
                        "d0": float(d0),
                        "unresolved_danger_count": int(len(danger)),
                        "radial_no_triple_danger_sampled": len(danger) == 0,
                        "best_unresolved_profile": best,
                    }
                )
    return rows


def _aggregate_thresholds(rows: list[dict[str, Any]]) -> dict[str, Any]:
    passing = [row for row in rows if row["radial_no_triple_danger_sampled"]]
    failing = [row for row in rows if not row["radial_no_triple_danger_sampled"]]
    first_pass = min(
        passing,
        key=lambda row: (float(row["r0"]), float(row["high_shell_eta"]), float(row["d0"])),
        default=None,
    )
    worst_fail = max(
        failing,
        key=lambda row: int(row["unresolved_danger_count"]),
        default=None,
    )
    return {
        "threshold_row_count": int(len(rows)),
        "passing_threshold_count": int(len(passing)),
        "failing_threshold_count": int(len(failing)),
        "first_passing_threshold": first_pass,
        "worst_failing_threshold": worst_fail,
    }


def _high_radial_low_d_summary(profiles: list[dict[str, Any]], c0: float) -> dict[str, Any]:
    high_radial_low_d = [
        profile
        for profile in profiles
        if _is_high_radial(profile, 1.5, 0.10) and _is_low_d(profile, 3.0)
    ]
    low_frame = [profile for profile in high_radial_low_d if _is_low_frame(profile, c0)]
    best_low_frame = min(low_frame, key=lambda p: float(p["lambda_min_kn_a"])) if low_frame else None
    min_lmin = min((_finite(p.get("lambda_min_kn_a")) for p in high_radial_low_d), default=None)
    min_lmin = min_lmin if isinstance(min_lmin, float) else None
    return {
        "condition": "radial_effective_scale >= 1.5 or high_shell_mass_fraction >= 0.10, and D <= 3.0",
        "profile_count": int(len(high_radial_low_d)),
        "low_frame_profile_count": int(len(low_frame)),
        "min_lambda_min_kn_a": min_lmin,
        "best_low_frame_profile": best_low_frame,
        "status": "unresolved-danger-present" if low_frame else "no-low-frame-sampled",
    }


def _schur_condition_summary(schur: dict[str, Any], profiles: list[dict[str, Any]]) -> dict[str, Any]:
    rows = [row for row in schur.get("rows", []) if isinstance(row, dict)]
    ok_rows = [row for row in rows if row.get("status") == OK_STATUS]
    unresolved_shells = sorted(
        {
            int(profile["shell"])
            for profile in profiles
            if profile.get("triple_danger") is True and isinstance(profile.get("shell"), int)
        }
    )
    conditioned = [row for row in ok_rows if int(row.get("shell", -1)) in unresolved_shells]
    return {
        "source_contract": schur.get("contract"),
        "source_status": schur.get("status"),
        "source_ok": bool(schur.get("ok")),
        "unresolved_danger_shells": unresolved_shells,
        "schur_rows": int(len(rows)),
        "schur_ok_rows": int(len(ok_rows)),
        "conditioned_ok_rows": int(len(conditioned)),
        "conditioned_schur_support_available": bool(conditioned),
        "status": "unavailable" if not conditioned else "telemetry-only",
        "gap": (
            "existing Schur audit has no OK rows on corrected unresolved-danger shells"
            if not conditioned
            else "Schur rows are empirical only and non-promoting"
        ),
    }


def _residence_condition_summary(residence: dict[str, Any], profiles: list[dict[str, Any]]) -> dict[str, Any]:
    unresolved = [profile for profile in profiles if profile.get("triple_danger") is True]
    by_shell: dict[int, list[dict[str, Any]]] = {}
    for profile in unresolved:
        shell = profile.get("shell")
        if isinstance(shell, int):
            by_shell.setdefault(shell, []).append(profile)
    shell_rows = []
    for shell, shell_profiles in sorted(by_shell.items()):
        diss = [_finite(profile.get("dissipation_proxy")) for profile in shell_profiles]
        diss = [value for value in diss if value is not None]
        radial = [_finite(profile.get("radial_effective_scale")) for profile in shell_profiles]
        radial = [value for value in radial if value is not None]
        shell_rows.append(
            {
                "shell": int(shell),
                "unresolved_profile_count": int(len(shell_profiles)),
                "dissipation_proxy_min": min(diss) if diss else None,
                "dissipation_proxy_mean": sum(diss) / len(diss) if diss else None,
                "radial_effective_scale_max": max(radial) if radial else None,
            }
        )
    return {
        "source_contract": residence.get("contract"),
        "source_status": residence.get("status"),
        "source_ok": bool(residence.get("ok")),
        "wall1_status": residence.get("aggregate", {}).get("wall1_status"),
        "wall2_status": residence.get("aggregate", {}).get("wall2_status"),
        "unresolved_profile_count": int(len(unresolved)),
        "shell_rows": shell_rows,
        "residence_time_exclusion_status": "unproved",
        "status": "counterpressure-present" if unresolved else "no-unresolved-radial-danger-sampled",
        "gap": "need a time-integrated high-radial residence lemma tying these D costs to finite energy budget",
    }


def main() -> int:
    args = _parse_args()
    errors: list[str] = []
    warnings: list[str] = []
    try:
        optimizer = _read_json(args.optimizer_json)
        schur = _read_json(args.schur_json)
        residence = _read_json(args.residence_json)
    except Exception as exc:  # noqa: BLE001
        errors.append(str(exc))
        optimizer = {}
        schur = {}
        residence = {}

    profiles = _profiles(optimizer)
    if not profiles:
        errors.append("optimizer profile_samples are empty")
    c0 = float(optimizer.get("parameters", {}).get("c0", 0.25))
    threshold_rows = _threshold_sweep(profiles, c0) if profiles else []
    unresolved = [profile for profile in profiles if profile.get("triple_danger") is True]
    angular_artifacts = [profile for profile in profiles if profile.get("angular_multiplicity_artifact") is True]
    payload = {
        "script_name": SCRIPT_NAME,
        "contract": CONTRACT,
        "route_decision": ROUTE_DECISION,
        "schema_version": SCHEMA_VERSION,
        "authority": AUTHORITY,
        "control_card": CONTROL_CARD,
        "inputs": {
            "optimizer_json": str(args.optimizer_json),
            "schur_json": str(args.schur_json),
            "residence_json": str(args.residence_json),
            "output_json": str(args.output_json),
        },
        "status": ERROR_STATUS if errors else OK_STATUS,
        "ok": not errors,
        "errors": errors,
        "warnings": warnings,
        "aggregate": {
            "profile_count": int(len(profiles)),
            "unresolved_danger_count": int(len(unresolved)),
            "angular_multiplicity_artifact_count": int(len(angular_artifacts)),
            "radial_no_triple_danger_status": "unproved",
            "radial_no_triple_danger_sampled": len(unresolved) == 0,
            "theorem_promoted": False,
            "full_ns_promoted": False,
            "clay_promoted": False,
        },
        "threshold_sweep": {
            "rows": threshold_rows,
            "aggregate": _aggregate_thresholds(threshold_rows),
        },
        "high_radial_low_d_optimizer": _high_radial_low_d_summary(profiles, c0) if profiles else {},
        "schur_conditioned_on_high_radial": _schur_condition_summary(schur, profiles) if profiles else {},
        "residence_conditioned_on_radial_scale": _residence_condition_summary(residence, profiles) if profiles else {},
    }
    args.output_json.parent.mkdir(parents=True, exist_ok=True)
    args.output_json.write_text(_json_text(payload, args.pretty) + "\n", encoding="utf-8")
    print(_json_text(payload, args.pretty))
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
