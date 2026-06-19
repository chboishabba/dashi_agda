#!/usr/bin/env python3
"""Summarize empirical NS boundary lambda3/F123 diagnostics.

This script reads one required Lambda-3 diagnostic JSON and an optional
F123 diagnostic JSON, validates authority metadata, extracts key status/numeric
fields, emits a deterministic summary JSON, and optionally a Markdown digest.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_boundary_empirical_summary.py"
CONTRACT = "ns_boundary_empirical_summary"
CONTROL_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
NUMERIC_STAT_KEYS = ("min", "max", "mean", "sum", "count", "std", "std_err")


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lambda3-json", type=Path, required=True, help="Required lambda3 diagnostic JSON")
    parser.add_argument("--f123-json", type=Path, help="Optional F123 diagnostic JSON")
    parser.add_argument("--output", type=Path, required=True, help="Required JSON summary output path")
    parser.add_argument(
        "--markdown-output",
        type=Path,
        help="Optional Markdown summary output path",
    )
    return parser.parse_args()


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    with path.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"JSON root is not an object: {path}")
    return data


def _sort_json_text(payload: Any) -> str:
    return json.dumps(payload, sort_keys=True, indent=2) + "\n"


def _coerce_float(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        if isinstance(value, float) and math.isfinite(value) is False:
            return None
        return float(value)
    return None


def _extract_authority(payload: dict[str, Any]) -> dict[str, Any] | None:
    if "authority" in payload and isinstance(payload["authority"], dict):
        return payload["authority"]
    metadata = payload.get("metadata")
    if isinstance(metadata, dict):
        authority = metadata.get("authority")
        if isinstance(authority, dict):
            return authority
    return None


def _validate_authority(source: str, payload: dict[str, Any]) -> tuple[bool, list[str], dict[str, Any]]:
    warnings: list[str] = []
    authority = _extract_authority(payload)
    if authority is None:
        warnings.append(f"{source}:authority_missing")
        return False, warnings, {"present": False}

    checks: dict[str, Any] = {"present": True}
    checks["empirical_non_promoting"] = authority.get("empirical_non_promoting")
    checks["promoted"] = authority.get("promoted")
    checks["clay_authority"] = authority.get("clay_authority")
    checks["theorem_authority"] = authority.get("theorem_authority")
    checks["truth_authority"] = authority.get("truth_authority")
    checks["runtime_authority"] = authority.get("runtime_authority")

    valid = True
    if checks["empirical_non_promoting"] is not True:
        warnings.append(
            f"{source}:authority_empirical_non_promoting_invalid="
            f"{checks['empirical_non_promoting']!r}"
        )
        valid = False
    if checks["promoted"] is not False:
        warnings.append(f"{source}:authority_promoted_invalid={checks['promoted']!r}")
        valid = False

    for key, label in (
        ("clay_authority", "clay"),
        ("theorem_authority", "theorem"),
        ("truth_authority", "truth"),
        ("runtime_authority", "runtime"),
    ):
        if key in authority and authority[key] is not False:
            warnings.append(f"{source}:{label}_authority_must_be_false={authority[key]!r}")
            valid = False

    if authority.get("candidate_only") is not None:
        checks["candidate_only"] = authority["candidate_only"]

    checks["raw"] = dict(sorted(authority.items()))
    return valid, warnings, checks


def _extract_control_fields(source: str, payload: dict[str, Any]) -> tuple[dict[str, str], list[str]]:
    control: dict[str, str] = {}
    warnings: list[str] = []
    for key in CONTROL_KEYS:
        value = payload.get(key)
        if value is None:
            warnings.append(f"{source}:missing_{key}_field")
        elif isinstance(value, str):
            control[key] = value
        else:
            warnings.append(f"{source}:{key}_not_string")
            control[key] = str(value)
    return control, warnings


def _collect_stats_fields(name: str, stats: dict[str, Any]) -> dict[str, float]:
    values: dict[str, float] = {}
    for stat in NUMERIC_STAT_KEYS:
        if stat in stats:
            value = _coerce_float(stats[stat])
            if value is not None:
                values[stat] = value
    if values:
        return {f"{name}.{k}": v for k, v in values.items()}
    return {}


def _extract_key_metrics(payload: dict[str, Any]) -> dict[str, Any]:
    scalar_candidates = (
        "status",
        "script",
        "contract",
        "route_decision",
        "frame",
        "component_id",
        "component_count",
        "component_cell_count",
        "boundary_cell_count",
        "tight_band_cell_count",
        "lambda3_min_abs",
        "min_g12",
        "min_rho",
        "lambda2_band",
        "lambda3_gap_threshold",
        "beta",
        "c_empirical_proxy",
        "c_empirical_true",
        "denominator_proxy_to_true_ratio",
        "numerator_int_boundary_Bk_dH2",
        "lambda3_bounded_away_from_zero",
    )
    metrics: dict[str, Any] = {}
    for key in scalar_candidates:
        if key in payload:
            metrics[key] = payload[key]

    for key, value in payload.items():
        if key.endswith("_stats") and isinstance(value, dict):
            metrics.update(_collect_stats_fields(key, value))
    if "dominance" in payload and isinstance(payload["dominance"], dict):
        dominance = payload["dominance"]
        if isinstance(dominance, dict):
            for dkey in ("ratio", "status", "count", "dominated", "meets_threshold"):
                if dkey in dominance:
                    metrics[f"dominance.{dkey}"] = dominance[dkey]
    if "notes" in payload and isinstance(payload["notes"], list) and payload["notes"]:
        metrics["notes_count"] = len(payload["notes"])
    return metrics


def _collect_source_summary(
    source: str,
    payload: dict[str, Any],
    optional: bool,
) -> tuple[dict[str, Any], bool]:
    warnings: list[str] = []
    summary: dict[str, Any] = {"source": source, "path": source, "optional": optional}

    control, control_warnings = _extract_control_fields(source, payload)
    warnings.extend(control_warnings)
    summary["control"] = control

    status = payload.get("status")
    summary["status"] = status
    if optional and status is None:
        warnings.append(f"{source}:optional_status_missing")
    elif not optional and status is None:
        warnings.append(f"{source}:status_missing")

    auth_ok, auth_warnings, auth_checks = _validate_authority(source, payload)
    warnings.extend(auth_warnings)
    summary["authority"] = auth_checks
    summary["authority_ok"] = bool(auth_ok)
    summary["authority_raw"] = _extract_authority(payload) or {}
    summary["warnings"] = sorted(set(w for w in warnings if w))
    summary["metrics"] = _extract_key_metrics(payload)
    summary["errors"] = payload.get("errors") if isinstance(payload.get("errors"), list) else []

    valid = auth_ok and (status is not None if not optional else True)
    return summary, valid


def _build_markdown(summary: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append(f"# {CONTRACT} summary")
    lines.append("")
    lines.append(f"- lambda3 JSON: `{summary['inputs']['lambda3']['path']}`")
    if summary["inputs"]["f123"]["path"] is None:
        lines.append("- f123 JSON: *(optional; not provided)*")
    else:
        lines.append(f"- f123 JSON: `{summary['inputs']['f123']['path']}`")
    lines.append("")
    lines.append(f"- overall status: `{summary['status']}`")
    lines.append("")
    lines.append("## Validation")
    lines.append("")
    for key, value in sorted(summary["validation"].items()):
        lines.append(f"- `{key}`: `{value}`")
    lines.append("")
    lines.append("## Warnings")
    lines.append("")
    if summary["warnings"]:
        for item in summary["warnings"]:
            lines.append(f"- {item}")
    else:
        lines.append("- none")

    for name in ("lambda3", "f123"):
        source = summary[name]
        lines.append("")
        lines.append(f"## {name}")
        lines.append("")
        lines.append(f"- status: `{source.get('status', None)!r}`")
        lines.append(f"- authority_ok: `{source['authority_ok']}`")
        lines.append(f"- source_path: `{source['path']}`")
        lines.append("")
        lines.append("### Control card")
        for key in CONTROL_KEYS:
            value = source.get("control", {}).get(key, "(missing)")
            lines.append(f"- {key}: {value}")
        if source.get("metrics"):
            lines.append("")
            lines.append("### Key fields")
            for metric, value in sorted(source["metrics"].items()):
                lines.append(f"- `{metric}`: `{value!r}`")
        if source.get("errors"):
            lines.append("")
            lines.append("### Source warnings")
            for item in source.get("warnings", []):
                lines.append(f"- {item}")

    return "\n".join(lines) + "\n"


def _build_summary(lambda3_path: Path, f123_path: Path | None) -> dict[str, Any]:
    warnings: list[str] = []
    lambda3_payload = _read_json(lambda3_path)
    lambda3_summary, lambda3_valid = _collect_source_summary("lambda3", lambda3_payload, optional=False)
    lambda3_summary["path"] = str(lambda3_path)

    f123_summary: dict[str, Any]
    f123_valid = True
    if f123_path is None:
        warnings.append("f123_json_not_provided")
        f123_summary = {
            "optional": True,
            "path": None,
            "status": None,
            "authority": {"present": False},
            "authority_ok": True,
            "authority_raw": {},
            "control": {},
            "metrics": {},
            "warnings": ["f123_json_not_provided"],
            "errors": [],
        }
    else:
        try:
            f123_payload = _read_json(f123_path)
        except (FileNotFoundError, ValueError) as exc:
            warnings.append(f"f123_json_invalid:{exc}")
            f123_summary = {
                "optional": True,
                "path": str(f123_path),
                "status": None,
                "authority": {"present": False},
                "authority_ok": False,
                "authority_raw": {},
                "control": {},
                "metrics": {},
                "warnings": [str(exc)],
                "errors": [str(exc)],
            }
            f123_valid = False
        else:
            f123_summary, f123_valid = _collect_source_summary(
                "f123", f123_payload, optional=True
            )
            f123_summary["path"] = str(f123_path)

    warnings.extend(lambda3_summary["warnings"])
    warnings.extend(f123_summary["warnings"])

    lambda3_status_ok = lambda3_summary.get("status") == "ok"
    f123_status_ok = f123_summary.get("status") in (None, "ok")

    status_counts: dict[str, int] = {}
    for src in (lambda3_summary, f123_summary):
        src_status = src.get("status")
        if src_status is None:
            continue
        status_counts[str(src_status)] = status_counts.get(str(src_status), 0) + 1

    validation = {
        "lambda3_loaded": True,
        "lambda3_authority_ok": bool(lambda3_summary["authority_ok"]),
        "lambda3_status_present": lambda3_summary.get("status") is not None,
        "lambda3_status_ok": lambda3_status_ok,
        "f123_status_ok": f123_status_ok,
        "f123_loaded": f123_summary.get("path") is not None,
        "f123_authority_ok": bool(f123_summary["authority_ok"]),
        "overall_pass": bool(lambda3_valid and f123_valid and lambda3_status_ok and f123_status_ok),
    }
    summary = {
        "contract": CONTRACT,
        "schema_version": "1.0.0",
        "script": SCRIPT_NAME,
        "authority": {
            "candidate_only": True,
            "empirical_non_promoting": True,
            "truth_authority": False,
            "theorem_authority": False,
            "clay_authority": False,
            "runtime_authority": False,
            "promoted": False,
        },
        "inputs": {
            "lambda3": {"path": str(lambda3_path), "loaded": True},
            "f123": {"path": None if f123_path is None else str(f123_path), "loaded": f123_path is not None},
        },
        "status": "ok" if validation["overall_pass"] else "warning",
        "validation": validation,
        "lambda3": lambda3_summary,
        "f123": f123_summary,
        "status_counts": status_counts,
        "warnings": sorted(set(warnings)),
        "lambda3_distribution_empirical": True,
        "lambda3_distribution_promoting": False,
        "h_delta1_hypothesis": True,
        "h_delta1_promoting": False,
        "f123_absorption_support_only": True,
        "commutator_comparison_measured": False,
        "commutator_comparison_proxy_unavailable": True,
        "korn_level_set": False,
        "collapse_impossible": False,
        "clay_promotion": False,
        "O": "Summarize the empirical NS boundary lambda3 and F123 diagnostic outputs.",
        "R": "Preserve fail-closed empirical evidence without theorem or Clay promotion.",
        "C": SCRIPT_NAME,
        "S": "Lambda3 and F123 JSON payloads are validated for authority metadata and status.",
        "L": "ok summary requires both supplied diagnostics to be ok and non-promoting.",
        "P": "FAIL_CLOSED_NS_BOUNDARY_LAMBDA3_F123_EMPIRICAL_SUMMARY",
        "G": "No KornLevelSet, collapseImpossible, or Clay promotion is permitted by this summary.",
        "F": "Remaining gaps are analytic: h_delta1, commutator comparison, KornLevelSet, and collapseImpossible stay open.",
    }
    summary["status_counts"]["total_sources"] = 1 + (1 if f123_summary.get("path") else 0)
    return summary


def main() -> int:
    args = _parse_args()
    try:
        summary = _build_summary(args.lambda3_json, args.f123_json)
    except (OSError, ValueError) as exc:
        failure = {
            "contract": CONTRACT,
            "schema_version": "1.0.0",
            "status": "error",
            "script": SCRIPT_NAME,
            "error": str(exc),
        }
        args.output.write_text(_sort_json_text(failure), encoding="utf-8")
        print(f"summary generation failed: {exc}")
        return 2

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(_sort_json_text(summary), encoding="utf-8")

    if args.markdown_output is not None:
        args.markdown_output.parent.mkdir(parents=True, exist_ok=True)
        args.markdown_output.write_text(_build_markdown(summary), encoding="utf-8")

    print(f"written: {args.output}")
    if args.markdown_output is not None:
        print(f"markdown: {args.markdown_output}")

    if summary["status"] in {"ok", "warning"}:
        return 0 if summary["validation"]["overall_pass"] else 1
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
