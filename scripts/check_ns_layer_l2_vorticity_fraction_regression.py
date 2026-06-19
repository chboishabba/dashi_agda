#!/usr/bin/env python3
"""Regression checker for Calc 8 layer L2 vorticity fraction JSON."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any, Iterable


SCRIPT_NAME = "scripts/check_ns_layer_l2_vorticity_fraction_regression.py"
CONTRACT = "check_ns_layer_l2_vorticity_fraction_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"
EXPECTED_FRAME_COUNT = 13
EXPECTED_EPS_BANDS = (0.001, 0.01, 0.1, 1.0)

CHECK_CARD_KEYS = ("O", "R", "C", "S", "L", "P", "G", "F")

FRAME_COUNT_KEYS = (
    "frame_count",
    "available_frame_count",
    "processed_frame_count",
    "row_count",
)

EPS_BAND_KEYS = (
    "eps_bands",
    "eps_band",
    "eps_values",
    "eps_levels",
    "epsilon_bands",
    "epsilon_values",
    "epsilon_levels",
    "bands",
)

TOTAL_OMEGA_L2_KEYS = (
    "total_omega_l2",
    "omega_l2_total",
    "total_omega_l2_norm",
    "omega_l2_norm_total",
    "total_omega_l2_sq",
    "omega_l2_sq_total",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "json_path",
        nargs="?",
        type=Path,
        help="Path to the layer L2 vorticity fraction JSON.",
    )
    parser.add_argument(
        "--json-path",
        type=Path,
        dest="json_path_kw",
        help="Path to the layer L2 vorticity fraction JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=None,
        help="Optional regression receipt output path.",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="Pretty-print the JSON receipt.",
    )
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


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    prefix = _join_path(path)
    warnings.append(f"{prefix}: {message}" if prefix else message)


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _coerce_finite_number(value: Any) -> float | None:
    if isinstance(value, bool) or value is None:
        return None
    if isinstance(value, (int, float)):
        value_f = float(value)
    elif isinstance(value, str):
        try:
            value_f = float(value)
        except ValueError:
            return None
    else:
        return None
    if not math.isfinite(value_f):
        return None
    return value_f


def _find_field(payload: dict[str, Any], aliases: Iterable[str]) -> tuple[str | None, Any | None]:
    aliases_tuple = tuple(aliases)
    for alias in aliases_tuple:
        if alias in payload:
            return alias, payload[alias]

    normalized_aliases = {_normalize_key(alias): alias for alias in aliases_tuple}
    for key, value in payload.items():
        if isinstance(key, str) and _normalize_key(key) in normalized_aliases:
            return key, value
    return None, None


def _is_fraction_measure_key(normalized: str) -> bool:
    if "fraction" not in normalized:
        return False
    return not any(
        token in normalized
        for token in ("count", "number", "numerator", "denominator", "total", "sum")
    ) and "monotone" not in normalized


def _check_control_card(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> None:
    for key in CHECK_CARD_KEYS:
        value = payload.get(key)
        if not isinstance(value, str) or not value.strip():
            _record_error(errors, source + (key,), "must be a non-empty string")


def _check_status(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> None:
    status = payload.get("status")
    if not isinstance(status, str) or not status.strip():
        _record_error(errors, source + ("status",), "must be a non-empty string")
        return
    if status != OK_STATUS:
        _record_error(errors, source + ("status",), f"must be {OK_STATUS!r}, got {status!r}")


def _check_frame_count(payload: dict[str, Any], errors: list[str], warnings: list[str], source: tuple[Any, ...]) -> int | None:
    observed: int | None = None
    for key in FRAME_COUNT_KEYS:
        if key not in payload:
            continue
        value = payload[key]
        if isinstance(value, bool) or not isinstance(value, int):
            _record_error(errors, source + (key,), f"must be a nonnegative integer, got {value!r}")
            continue
        if value < 0:
            _record_error(errors, source + (key,), f"must be nonnegative, got {value}")
            continue
        observed = value if observed is None else observed
        if value != EXPECTED_FRAME_COUNT:
            _record_error(
                errors,
                source + (key,),
                f"must be {EXPECTED_FRAME_COUNT}, got {value}",
            )
    rows = payload.get("rows")
    if isinstance(rows, list):
        if observed is not None and len(rows) != observed:
            _record_error(errors, source + ("rows",), f"length {len(rows)} does not match frame count {observed}")
        elif observed is None and len(rows) != EXPECTED_FRAME_COUNT:
            _record_error(
                errors,
                source + ("rows",),
                f"length {len(rows)} must be {EXPECTED_FRAME_COUNT} when frame count is not explicit",
            )
        if len(rows) == EXPECTED_FRAME_COUNT:
            observed = EXPECTED_FRAME_COUNT
    elif rows is not None:
        _record_error(errors, source + ("rows",), f"must be a list, got {type(rows).__name__}")

    frames = payload.get("frames")
    if isinstance(frames, list):
        if observed is not None and len(frames) != observed:
            _record_error(
                errors,
                source + ("frames",),
                f"length {len(frames)} does not match frame count {observed}",
            )
        elif observed is None and len(frames) != EXPECTED_FRAME_COUNT:
            _record_error(
                errors,
                source + ("frames",),
                f"length {len(frames)} must be {EXPECTED_FRAME_COUNT} when frame count is not explicit",
            )
        if len(frames) == EXPECTED_FRAME_COUNT:
            observed = EXPECTED_FRAME_COUNT
    elif frames is not None:
        _record_error(errors, source + ("frames",), f"must be a list, got {type(frames).__name__}")

    if observed is None:
        warnings.append("no frame count or frame list was present")
    return observed


def _check_eps_bands(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> list[float]:
    expected = list(EXPECTED_EPS_BANDS)
    found_values: list[float] = []
    matched_key: str | None = None

    for key in EPS_BAND_KEYS:
        field_key, value = _find_field(payload, (key,))
        if field_key is None:
            continue
        matched_key = field_key
        if isinstance(value, dict):
            band_values: list[float] = []
            for band_key in value:
                band_value = _coerce_finite_number(band_key)
                if band_value is not None:
                    band_values.append(band_value)
            found_values = sorted(set(band_values))
            break
        if isinstance(value, (list, tuple)):
            band_values = []
            for item in value:
                band_value = _coerce_finite_number(item)
                if band_value is None:
                    _record_error(
                        errors,
                        source + (field_key,),
                        f"must contain finite numeric eps bands, got {item!r}",
                    )
                    continue
                band_values.append(band_value)
            found_values = sorted(set(band_values))
            break
        band_value = _coerce_finite_number(value)
        if band_value is not None:
            found_values = [band_value]
        else:
            _record_error(errors, source + (field_key,), f"must be numeric, got {value!r}")
        break

    if matched_key is None:
        _record_error(
            errors,
            source + ("eps_bands",),
            "missing eps band field (aliases: eps_bands, eps_values, eps_levels, epsilon_bands, epsilon_values, epsilon_levels, bands)",
        )
        return []

    missing = [value for value in expected if not any(math.isclose(value, item, rel_tol=0.0, abs_tol=1e-12) for item in found_values)]
    if missing:
        _record_error(
            errors,
            source + (matched_key,),
            f"must include eps bands {expected!r}; missing {missing!r}",
        )
    return found_values


def _check_fraction_like_value(
    value: Any,
    errors: list[str],
    path: tuple[Any, ...],
    *,
    lower: float = 0.0,
    upper: float = 1.0,
) -> float | None:
    value_f = _coerce_finite_number(value)
    if value_f is None:
        _record_error(errors, path, f"must be finite numeric, got {value!r}")
        return None
    if value_f < lower or value_f > upper:
        _record_error(errors, path, f"must lie in [{lower}, {upper}], got {value_f:.17g}")
        return None
    return value_f


def _check_total_omega_l2(payload: dict[str, Any], errors: list[str], source: tuple[Any, ...]) -> float | None:
    found_key, found_value = _find_field(payload, TOTAL_OMEGA_L2_KEYS)
    if found_key is None:
        _record_error(
            errors,
            source + ("total_omega_l2",),
            "missing total omega L2 field (aliases: total_omega_l2, omega_l2_total, total_omega_l2_norm, omega_l2_norm_total, total_omega_l2_sq, omega_l2_sq_total)",
        )
        return None
    value_f = _coerce_finite_number(found_value)
    if value_f is None:
        _record_error(errors, source + (found_key,), f"must be finite numeric, got {found_value!r}")
        return None
    if value_f <= 0.0:
        _record_error(errors, source + (found_key,), f"must be positive, got {value_f:.17g}")
        return None
    return value_f


def _walk_for_fraction_fields(
    node: Any,
    path: tuple[Any, ...],
    errors: list[str],
    fraction_values: list[float],
    omega_l2_candidates: list[tuple[tuple[Any, ...], float]],
) -> None:
    if isinstance(node, dict):
        for key, value in node.items():
            child_path = path + (key,)
            if isinstance(key, str):
                normalized = _normalize_key(key)
                if _is_fraction_measure_key(normalized):
                    if isinstance(value, (list, tuple)):
                        for index, item in enumerate(value):
                            fraction = _check_fraction_like_value(item, errors, child_path + (index,))
                            if fraction is not None:
                                fraction_values.append(fraction)
                    elif isinstance(value, dict):
                        for sub_key, sub_value in value.items():
                            fraction = _check_fraction_like_value(sub_value, errors, child_path + (sub_key,))
                            if fraction is not None:
                                fraction_values.append(fraction)
                    else:
                        fraction = _check_fraction_like_value(value, errors, child_path)
                        if fraction is not None:
                            fraction_values.append(fraction)

                if "omega" in normalized and "l2" in normalized and (
                    "total" in normalized or "sum" in normalized or "norm" in normalized or "layer" in normalized
                ):
                    fraction = _coerce_finite_number(value)
                    if fraction is not None:
                        omega_l2_candidates.append((child_path, fraction))
                    else:
                        _record_error(errors, child_path, f"must be finite numeric, got {value!r}")

            _walk_for_fraction_fields(value, child_path, errors, fraction_values, omega_l2_candidates)
        return
    if isinstance(node, list):
        for index, item in enumerate(node):
            _walk_for_fraction_fields(item, path + (index,), errors, fraction_values, omega_l2_candidates)


def _check_rows(payload: dict[str, Any], errors: list[str], warnings: list[str], source: tuple[Any, ...]) -> None:
    rows = payload.get("rows")
    if not isinstance(rows, list):
        return
    frame_values: list[int] = []
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            _record_error(errors, source + ("rows", index), f"must be an object, got {type(row).__name__}")
            continue
        frame = row.get("frame")
        if frame is not None:
            if isinstance(frame, bool) or not isinstance(frame, int):
                _record_error(errors, source + ("rows", index, "frame"), f"must be a nonnegative integer, got {frame!r}")
            elif frame < 0:
                _record_error(errors, source + ("rows", index, "frame"), f"must be nonnegative, got {frame}")
            else:
                frame_values.append(frame)
        status = row.get("status")
        if status is not None and status != OK_STATUS:
            _record_error(errors, source + ("rows", index, "status"), f"must be {OK_STATUS!r}, got {status!r}")

        for key, value in row.items():
            if not isinstance(key, str):
                continue
            normalized = _normalize_key(key)
            if _is_fraction_measure_key(normalized):
                _check_fraction_like_value(value, errors, source + ("rows", index, key))

            if "omega" in normalized and "l2" in normalized and (
                "total" in normalized or "sum" in normalized or "norm" in normalized
            ):
                omega_value = _coerce_finite_number(value)
                if omega_value is None:
                    _record_error(errors, source + ("rows", index, key), f"must be finite numeric, got {value!r}")
                elif omega_value <= 0.0:
                    _record_error(errors, source + ("rows", index, key), f"must be positive, got {omega_value:.17g}")

    if frame_values:
        expected_frames = list(range(min(frame_values), min(frame_values) + len(frame_values)))
        if sorted(frame_values) != expected_frames:
            warnings.append("row frame indices are not contiguous")
        if len(rows) == EXPECTED_FRAME_COUNT and sorted(frame_values) != list(range(EXPECTED_FRAME_COUNT)):
            warnings.append("row frame indices do not match the expected 0..12 range")


def validate_payload(payload: dict[str, Any]) -> tuple[list[str], list[str], dict[str, Any]]:
    errors: list[str] = []
    warnings: list[str] = []
    source = ()

    _check_control_card(payload, errors, source)
    _check_status(payload, errors, source)
    observed_frame_count = _check_frame_count(payload, errors, warnings, source)
    observed_eps_bands = _check_eps_bands(payload, errors, source)
    _check_rows(payload, errors, warnings, source)

    fraction_values: list[float] = []
    omega_l2_candidates: list[tuple[tuple[Any, ...], float]] = []
    _walk_for_fraction_fields(payload, (), errors, fraction_values, omega_l2_candidates)

    if not fraction_values:
        warnings.append("no fraction-valued fields were found")

    total_omega_l2 = _check_total_omega_l2(payload, errors, source)

    result = {
        "frame_count": observed_frame_count,
        "eps_bands": observed_eps_bands,
        "fraction_count": len(fraction_values),
        "min_fraction": min(fraction_values) if fraction_values else None,
        "max_fraction": max(fraction_values) if fraction_values else None,
        "total_omega_l2": total_omega_l2,
        "omega_l2_candidates": [(_join_path(path), value) for path, value in omega_l2_candidates],
    }
    return errors, warnings, result


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    try:
        args = _parse_args()
        path = args.json_path_kw if args.json_path_kw is not None else args.json_path
        if args.json_path is not None and args.json_path_kw is not None:
            raise ValueError("provide exactly one JSON path, not both positional and --json-path")
        if path is None:
            raise ValueError("missing required JSON path")
    except (ValueError, OSError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"json_path": None, "output_json": None},
            "changed_files": [],
            "expected_frame_count": EXPECTED_FRAME_COUNT,
            "expected_eps_bands": list(EXPECTED_EPS_BANDS),
            "O": "Worker 2 owns the Calc 8 layer L2 vorticity fraction JSON regression checker.",
            "R": "Validate status, frame coverage, epsilon bands, fraction bounds, and total omega L2.",
            "C": SCRIPT_NAME,
            "S": "This is an empirical regression gate, not a proof surface.",
            "L": "status -> frames -> eps bands -> fractions -> total omega L2.",
            "P": "FAIL_CLOSED_NS_LAYER_L2_VORTICITY_FRACTION_REGRESSION",
            "G": "No theorem, Clay, or promotion claim is inferred.",
            "F": "The checker only validates the recorded diagnostic JSON.",
        }
        print(json.dumps(result, sort_keys=True, indent=2 if getattr(args, "pretty", False) else None))
        return 1

    errors: list[str] = []
    warnings: list[str] = []
    inputs = {"json_path": str(path), "output_json": str(args.output_json) if args.output_json else None}
    changed_files = [str(path)]
    if args.output_json is not None:
        changed_files.append(str(args.output_json))

    try:
        payload = _load_json(path)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        errors.append(f"{path}: {exc}")
        validation = {
            "frame_count": None,
            "eps_bands": [],
            "fraction_count": 0,
            "min_fraction": None,
            "max_fraction": None,
            "total_omega_l2": None,
            "omega_l2_candidates": [],
        }
        status = ERROR_STATUS
    else:
        errors, warnings, validation = validate_payload(payload)
        status = ERROR_STATUS if errors else OK_STATUS

    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": sorted(set(errors)),
        "warnings": sorted(set(warnings)),
        "inputs": inputs,
        "changed_files": sorted(set(changed_files)),
        "expected_frame_count": EXPECTED_FRAME_COUNT,
        "expected_eps_bands": list(EXPECTED_EPS_BANDS),
        "validation": validation,
        "O": "Worker 2 owns the Calc 8 layer L2 vorticity fraction JSON regression checker.",
        "R": "Validate status, frame coverage, epsilon bands, fraction bounds, and total omega L2.",
        "C": SCRIPT_NAME,
        "S": "This is an empirical regression gate, not a proof surface.",
        "L": "status -> frames -> eps bands -> fractions -> total omega L2.",
        "P": "FAIL_CLOSED_NS_LAYER_L2_VORTICITY_FRACTION_REGRESSION",
        "G": "No theorem, Clay, or promotion claim is inferred.",
        "F": "The checker only validates the recorded diagnostic JSON.",
    }

    rendered = json.dumps(result, sort_keys=True, indent=2 if args.pretty else None)
    print(rendered)
    if args.output_json is not None:
        _write_json(args.output_json, result)
    return 0 if status == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
