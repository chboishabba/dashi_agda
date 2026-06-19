#!/usr/bin/env python3
"""Summarize the lambda2 carrier route implication from two JSON inputs.

The script is intentionally fail-closed: if the required quantile or signed
partition information cannot be recovered deterministically, it emits a
`broad_tube_required` route code with errors rather than guessing.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from pathlib import Path
from typing import Any


SCRIPT_NAME = "scripts/ns_lambda2_carrier_route_summary.py"
CONTRACT = "ns_lambda2_carrier_route_summary"
DEFAULT_OUTPUT = Path("outputs/ns_lambda2_carrier_route_summary.json")
TARGET_FRACTIONS = (0.05, 0.10, 0.25, 0.50)
REGION_KEYS = ("negative", "near_zero", "positive")
CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")
SHAHMUROV_INTAKE_PATTERNS = (
    "*Shahmurov*intake*.json",
    "*shahmurov*intake*.json",
    "*Shahmurov*claim*intake*.json",
    "*shahmurov*claim*intake*.json",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("quantile_json", type=Path, help="Weighted quantile JSON input.")
    parser.add_argument("partition_json", type=Path, help="Signed partition JSON input.")
    parser.add_argument(
        "--output",
        nargs="?",
        const=DEFAULT_OUTPUT,
        default=None,
        type=Path,
        help="Optional output JSON path. If given without a value, uses the default receipt path.",
    )
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON output.")
    return parser.parse_args()


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _join_path(path: tuple[Any, ...]) -> str:
    if not path:
        return ""
    label = ""
    for entry in path:
        if isinstance(entry, int):
            label += f"[{entry}]"
        else:
            if label:
                label += "."
            label += str(entry)
    return label


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    errors.append(f"{prefix}: {message}" if prefix else message)


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _find_shahmurov_intake_json(output_path: Path | None) -> Path | None:
    search_dir = output_path.parent if output_path is not None else Path.cwd()
    matches: list[Path] = []
    for pattern in SHAHMUROV_INTAKE_PATTERNS:
        matches.extend(search_dir.glob(pattern))
    candidates = sorted({path for path in matches if path.is_file()})
    return candidates[0] if candidates else None


def _walk_json_nodes(node: Any):
    yield node
    if isinstance(node, dict):
        for value in node.values():
            yield from _walk_json_nodes(value)
    elif isinstance(node, list):
        for value in node:
            yield from _walk_json_nodes(value)


def _extract_first_matching_value(node: Any, keys: tuple[str, ...]) -> Any | None:
    normalized_targets = {_normalize_key(key) for key in keys}
    for candidate in _walk_json_nodes(node):
        if isinstance(candidate, dict):
            for key, value in candidate.items():
                if _normalize_key(str(key)) in normalized_targets:
                    return value
    return None


def _as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)) and value in (0, 1):
        return bool(value)
    if isinstance(value, str):
        normalized = _normalize_key(value)
        if normalized in {"true", "yes", "verified", "peerreviewverified", "peerreviewed"}:
            return True
        if normalized in {"false", "no", "unverified", "pending", "unknown", "notverified"}:
            return False
    return None


def _shahmurov_external_claim_summary(output_path: Path | None) -> dict[str, Any]:
    intake_path = _find_shahmurov_intake_json(output_path)
    observed = intake_path is not None
    peer_review_verified = False

    if intake_path is not None:
        try:
            payload = _load_json(intake_path)
        except (OSError, ValueError, json.JSONDecodeError):
            payload = None
        if payload is not None:
            direct_bool = _as_bool(
                _extract_first_matching_value(
                    payload,
                    (
                        "external_claim_peer_review_verified",
                        "peer_review_verified",
                        "peerreviewverified",
                        "external_review_verified",
                        "review_verified",
                    ),
                )
            )
            if direct_bool is not None:
                peer_review_verified = direct_bool
            else:
                peer_review_status = _extract_first_matching_value(
                    payload,
                    (
                        "external_status",
                        "externalStatus",
                        "peer_review_status",
                        "peerReviewStatus",
                        "review_status",
                        "reviewStatus",
                        "status",
                    ),
                )
                if isinstance(peer_review_status, str):
                    normalized = _normalize_key(peer_review_status)
                    peer_review_verified = normalized in {
                        "verified",
                        "peerreviewverified",
                        "peerreviewed",
                        "reviewverified",
                        "externallyverified",
                    }

    return {
        "external_claim_route_observed": observed,
        "external_claim_peer_review_verified": peer_review_verified,
        "external_claim_promotion_allowed": False,
        "external_claim_route_code": "Shahmurov/SerrinFromQ2Control" if observed else None,
    }


def _coerce_number(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        number = float(value)
    elif isinstance(value, str):
        try:
            number = float(value)
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(number):
        return None
    return number


def _coerce_quantile_key(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        number = float(value)
        if 0.0 <= number <= 1.0:
            return number
        if 1.0 < number <= 100.0 and abs(number - round(number)) < 1e-12:
            integer = int(round(number))
            if integer in {5, 10, 25, 50}:
                return integer / 100.0
        return None
    if not isinstance(value, str):
        return None

    text = value.strip().lower()
    if not text:
        return None

    direct = re.fullmatch(r"(?:q|p|pct|percent)?(\d+(?:\.\d+)?)%?", text)
    if direct is not None:
        parsed = float(direct.group(1))
        if 0.0 <= parsed <= 1.0:
            return parsed
        if parsed in {5.0, 10.0, 25.0, 50.0}:
            return parsed / 100.0
        if parsed <= 100.0 and abs(parsed - round(parsed)) < 1e-12:
            integer = int(round(parsed))
            if integer in {5, 10, 25, 50}:
                return integer / 100.0
    try:
        parsed = float(text.rstrip("%"))
    except ValueError:
        return None
    if 0.0 <= parsed <= 1.0:
        return parsed
    if parsed in {5.0, 10.0, 25.0, 50.0}:
        return parsed / 100.0
    return None


def _first_numeric_scalar(node: Any) -> float | None:
    if isinstance(node, dict):
        for key in ("epsilon", "eps", "value", "quantile", "estimate", "threshold"):
            if key in node:
                number = _coerce_number(node[key])
                if number is not None:
                    return number
    return _coerce_number(node)


def _parse_quantile_rows(rows: list[Any]) -> dict[float, float] | None:
    mapping: dict[float, float] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        q_value = None
        eps_value = None
        for key, value in row.items():
            normalized = _normalize_key(str(key))
            if q_value is None and normalized in {"q", "p", "quantile", "percentile"}:
                q_value = _coerce_quantile_key(value)
            elif q_value is None and normalized in {"q05", "q10", "q25", "q50", "p05", "p10", "p25", "p50"}:
                q_value = _coerce_quantile_key(key)
                if q_value is None:
                    q_value = _coerce_quantile_key(value)
            if eps_value is None and normalized in {
                "epsilon",
                "eps",
                "value",
                "estimate",
                "threshold",
                "neededepsilon",
                "neededeps",
                "epsneeded",
            }:
                eps_value = _coerce_number(value)
        if q_value is None:
            for key in row:
                q_value = _coerce_quantile_key(key)
                if q_value is not None:
                    break
        if eps_value is None:
            eps_value = _first_numeric_scalar(row)
        if q_value is not None and eps_value is not None:
            mapping[q_value] = eps_value
    if all(target in mapping for target in TARGET_FRACTIONS):
        return {target: mapping[target] for target in TARGET_FRACTIONS}
    return None


def _parse_quantile_dict(node: dict[str, Any]) -> dict[float, float] | None:
    mapping: dict[float, float] = {}

    for key, value in node.items():
        q_value = _coerce_quantile_key(key)
        if q_value is None:
            continue
        eps_value = _first_numeric_scalar(value)
        if eps_value is None and isinstance(value, dict):
            for child_key in ("epsilon", "eps", "value", "estimate", "threshold"):
                if child_key in value:
                    eps_value = _coerce_number(value[child_key])
                    if eps_value is not None:
                        break
        if eps_value is not None:
            mapping[q_value] = eps_value

    if all(target in mapping for target in TARGET_FRACTIONS):
        return {target: mapping[target] for target in TARGET_FRACTIONS}
    return None


def _search_quantiles(node: Any) -> dict[float, float] | None:
    if isinstance(node, dict):
        summary = node.get("summary")
        if isinstance(summary, dict) and isinstance(summary.get("target_stats"), dict):
            target_stats = summary["target_stats"]
            mapping: dict[float, float] = {}
            for key, value in target_stats.items():
                target = _coerce_quantile_key(key)
                if target is None:
                    continue
                if isinstance(value, dict):
                    eps = _coerce_number(value.get("mean_eps_needed"))
                    if eps is None:
                        eps = _coerce_number(value.get("eps_needed"))
                    if eps is not None:
                        mapping[target] = eps
            if all(target in mapping for target in TARGET_FRACTIONS):
                return {target: mapping[target] for target in TARGET_FRACTIONS}
        for key in (
            "weighted_quantiles",
            "weighted_quantile",
            "quantiles",
            "quantile_map",
            "epsilon_quantiles",
            "eps_quantiles",
            "quantile_summary",
        ):
            if key in node:
                value = node[key]
                if isinstance(value, dict):
                    parsed = _parse_quantile_dict(value)
                    if parsed is not None:
                        return parsed
                elif isinstance(value, list):
                    parsed = _parse_quantile_rows(value)
                    if parsed is not None:
                        return parsed

        parsed = _parse_quantile_dict(node)
        if parsed is not None:
            return parsed
        for value in node.values():
            parsed = _search_quantiles(value)
            if parsed is not None:
                return parsed
        return None
    if isinstance(node, list):
        parsed = _parse_quantile_rows(node)
        if parsed is not None:
            return parsed
        for value in node:
            parsed = _search_quantiles(value)
            if parsed is not None:
                return parsed
    return None


def _parse_region_dict(node: dict[str, Any]) -> dict[str, float] | None:
    alias_map = {
        "negative": ("negative_fraction", "negative", "neg_fraction", "neg", "left_fraction", "left_share"),
        "near_zero": (
            "near_zero_fraction",
            "nearzero_fraction",
            "zero_fraction",
            "neutral_fraction",
            "carrier_fraction",
            "mid_fraction",
            "tube_fraction",
        ),
        "positive": ("positive_fraction", "positive", "pos_fraction", "pos", "right_fraction", "right_share"),
    }

    fractions: dict[str, float] = {}
    counts: dict[str, float] = {}
    total_count: float | None = None

    for region, aliases in alias_map.items():
        for key, value in node.items():
            normalized = _normalize_key(str(key))
            if normalized in {_normalize_key(alias) for alias in aliases}:
                number = _coerce_number(value)
                if number is not None:
                    fractions[region] = number
                    break
    count_alias_map = {
        "negative": ("negative_count", "neg_count", "n_negative", "negative_n"),
        "near_zero": ("near_zero_count", "nearzero_count", "zero_count", "neutral_count", "carrier_count"),
        "positive": ("positive_count", "pos_count", "n_positive", "positive_n"),
    }
    total_aliases = ("total_count", "count", "n", "total", "samples", "sample_count")
    for region, aliases in count_alias_map.items():
        for key, value in node.items():
            normalized = _normalize_key(str(key))
            if normalized in {_normalize_key(alias) for alias in aliases}:
                number = _coerce_number(value)
                if number is not None:
                    counts[region] = number
                    break
    for key, value in node.items():
        normalized = _normalize_key(str(key))
        if normalized in {_normalize_key(alias) for alias in total_aliases}:
            total_count = _coerce_number(value)
            if total_count is not None:
                break

    if len(fractions) == 3:
        return fractions
    if len(counts) == 3:
        total = total_count if total_count is not None else sum(counts.values())
        if total > 0.0:
            return {region: counts[region] / total for region in REGION_KEYS}
    return None


def _search_regions(node: Any) -> dict[str, float] | None:
    if isinstance(node, dict):
        summary = node.get("summary")
        if isinstance(summary, dict) and isinstance(summary.get("region_stats"), dict):
            region_stats = summary["region_stats"]
            required = {
                "negative": "lambda2_negative_total",
                "near_zero": "lambda2_near_zero_total",
                "positive": "lambda2_positive_total",
            }
            fractions: dict[str, float] = {}
            for region, key in required.items():
                value = region_stats.get(key)
                if isinstance(value, dict):
                    mean = _coerce_number(value.get("mean"))
                    if mean is not None:
                        fractions[region] = mean
            if len(fractions) == 3:
                return fractions
        parsed = _parse_region_dict(node)
        if parsed is not None:
            return parsed
        for key in ("region_fractions", "fractions", "signed_fractions", "partition", "signed_partition", "regions"):
            if key in node:
                child = node[key]
                if isinstance(child, dict):
                    parsed = _parse_region_dict(child)
                    if parsed is not None:
                        return parsed
                elif isinstance(child, list) and len(child) == 3:
                    values = [_coerce_number(item) for item in child]
                    if all(value is not None for value in values):
                        return {
                            "negative": float(values[0]),
                            "near_zero": float(values[1]),
                            "positive": float(values[2]),
                        }
        for value in node.values():
            parsed = _search_regions(value)
            if parsed is not None:
                return parsed
        return None
    if isinstance(node, list):
        if len(node) == 3:
            values = [_coerce_number(item) for item in node]
            if all(value is not None for value in values):
                return {
                    "negative": float(values[0]),
                    "near_zero": float(values[1]),
                    "positive": float(values[2]),
                }
        for value in node:
            parsed = _search_regions(value)
            if parsed is not None:
                return parsed
    return None


def _validate_region_fractions(region_fractions: dict[str, float]) -> list[str]:
    errors: list[str] = []
    for region in REGION_KEYS:
        value = region_fractions.get(region)
        if value is None or not math.isfinite(value):
            errors.append(f"missing or non-finite fraction for {region}")
            continue
        if value < 0.0 or value > 1.0:
            errors.append(f"{region} fraction must lie in [0, 1], got {value:.17g}")
    signed_total = region_fractions.get("negative", 0.0) + region_fractions.get("positive", 0.0)
    if math.isfinite(signed_total) and abs(signed_total - 1.0) > 1.0e-6:
        errors.append(f"negative and positive fractions must sum to 1, got {signed_total:.17g}")
    return errors


def _route_code(region_fractions: dict[str, float], eps_needed: dict[str, float], errors: list[str]) -> tuple[str, str]:
    if errors:
        return "broad_tube_required", "fail-closed: input errors require a broad tube route"

    negative = region_fractions["negative"]
    near_zero = region_fractions["near_zero"]
    positive = region_fractions["positive"]
    strict_supported = near_zero >= 0.5 and negative <= 0.25 and positive <= 0.25
    if strict_supported:
        return (
            "strict_carrier_weak",
            (
                "near-zero mass dominates the signed partition, so the strict carrier "
                "route remains the weakest viable implication"
            ),
        )
    return (
        "broad_tube_required",
        (
            "signed mass is too dispersed away from the near-zero carrier, so a broader "
            "tube is required to support the route implication"
        ),
    )


def _json_text(payload: dict[str, Any], pretty: bool) -> str:
    if pretty:
        return json.dumps(payload, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
    return json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)


def _write_json(path: Path, payload: dict[str, Any], pretty: bool) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rendered = _json_text(payload, pretty=pretty)
    path.write_text(rendered + "\n", encoding="utf-8")


def main() -> int:
    try:
        args = _parse_args()
    except (ValueError, OSError) as exc:
        error_payload = {
            "contract": CONTRACT,
            "status": "error",
            "errors": [str(exc)],
            "warnings": [],
            "changed_files": [],
            "inputs": {"quantile_json": None, "partition_json": None, "output": None},
            "route_code": "broad_tube_required",
            "route_implication": {
                "code": "broad_tube_required",
                "reason": "argument parsing failed",
            },
            "eps_needed_for_omega_l2": {f"p{int(fraction * 100):02d}": None for fraction in TARGET_FRACTIONS},
            "region_fractions": {"negative": None, "near_zero": None, "positive": None},
            "O": "Worker 6 owns the lambda2 carrier route summary.",
            "R": "Summarize the epsilon thresholds and signed-region fractions from two recorded JSON inputs.",
            "C": SCRIPT_NAME,
            "S": "Fail-closed empirical summary; no theorem is inferred.",
            "L": "quantile eps -> signed partition fractions -> route code.",
            "P": "FAIL_CLOSED_NS_LAMBDA2_CARRIER_ROUTE_SUMMARY",
            "G": "Route code remains conservative when parsing fails.",
            "F": "The script only synthesizes the recorded diagnostics.",
        }
        print(_json_text(error_payload, pretty=False))
        return 1

    errors: list[str] = []
    warnings: list[str] = []
    changed_files: list[str] = []
    external_claim = _shahmurov_external_claim_summary(args.output)
    inputs = {
        "quantile_json": str(args.quantile_json),
        "partition_json": str(args.partition_json),
        "output": str(args.output) if args.output is not None else None,
    }
    if args.output is not None:
        changed_files.append(str(args.output))

    try:
        quantile_payload = _load_json(args.quantile_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"{args.quantile_json}: {exc}")
        quantile_map = {fraction: None for fraction in TARGET_FRACTIONS}
    else:
        quantile_map = _search_quantiles(quantile_payload)
        if quantile_map is None:
            errors.append(
                f"{args.quantile_json}: could not recover epsilon values for {TARGET_FRACTIONS!r}"
            )
            quantile_map = {fraction: None for fraction in TARGET_FRACTIONS}

    try:
        partition_payload = _load_json(args.partition_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"{args.partition_json}: {exc}")
        region_fractions = {region: None for region in REGION_KEYS}
    else:
        region_fractions = _search_regions(partition_payload)
        if region_fractions is None:
            errors.append(
                f"{args.partition_json}: could not recover negative/near_zero/positive fractions"
            )
            region_fractions = {region: None for region in REGION_KEYS}

    if all(value is not None for value in region_fractions.values()):
        errors.extend(_validate_region_fractions({k: float(v) for k, v in region_fractions.items()}))

    eps_needed = {
        f"p{int(fraction * 100):02d}": (None if quantile_map[fraction] is None else float(quantile_map[fraction]))
        for fraction in TARGET_FRACTIONS
    }

    if errors:
        route_code = "broad_tube_required"
        route_reason = "fail-closed: route implication cannot be strengthened from incomplete input"
    else:
        route_code, route_reason = _route_code(
            {k: float(v) for k, v in region_fractions.items()},
            {k: float(v) for k, v in eps_needed.items() if v is not None},
            errors,
        )

    result = {
        "contract": CONTRACT,
        "status": "error" if errors else "ok",
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "changed_files": sorted(set(changed_files)),
        "inputs": inputs,
        "eps_needed_for_omega_l2": eps_needed,
        "region_fractions": region_fractions,
        "route_code": route_code,
        "route_implication": {
            "code": route_code,
            "reason": route_reason,
            "fail_closed": True,
            "strict_supported": route_code == "strict_carrier_weak",
            "broad_tube_required": route_code == "broad_tube_required",
        },
        "summary": {
            "omega_l2_fraction_targets": [0.05, 0.10, 0.25, 0.50],
            "negative_fraction": region_fractions["negative"],
            "near_zero_fraction": region_fractions["near_zero"],
            "positive_fraction": region_fractions["positive"],
            "route_code": route_code,
            **external_claim,
        },
        **external_claim,
        "O": "Worker 6 owns the lambda2 carrier route summary.",
        "R": "Summarize the epsilon thresholds and signed-region fractions from two recorded JSON inputs.",
        "C": SCRIPT_NAME,
        "S": "Fail-closed empirical summary; no theorem is inferred.",
        "L": "quantile eps -> signed partition fractions -> route code.",
        "P": "FAIL_CLOSED_NS_LAMBDA2_CARRIER_ROUTE_SUMMARY",
        "G": "Route code remains conservative when the carrier partition is not strong enough.",
        "F": "The script only synthesizes the recorded diagnostics.",
    }

    rendered = _json_text(result, pretty=args.pretty)
    print(rendered)

    if args.output is not None:
        _write_json(args.output, result, pretty=args.pretty)

    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
