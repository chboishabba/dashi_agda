#!/usr/bin/env python3
"""Regression checker for Shahmurov claim intake JSON."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any, Iterable


SCRIPT_NAME = "scripts/check_ns_shahmurov_claim_intake_regression.py"
CONTRACT = "check_ns_shahmurov_claim_intake_regression"
OK_STATUS = "ok"
ERROR_STATUS = "error"

REQUIRED_ARXIV_IDS = ("2605.01875", "2605.01873")
ALLOWED_STATUS_VALUES = {"fail-closed", "unverified"}
REQUIRED_FALSE_FLAGS = (
    "peer_review_verified",
    "clay_promotion",
    "dashi_route_superseded",
)
MANUAL_CHECK_KEYS = (
    "manual_checks",
    "manual_review_checks",
    "required_manual_checks",
    "manual_checklist",
)


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input_json",
        type=Path,
        help="Path to the Shahmurov claim intake JSON.",
    )
    parser.add_argument(
        "--output-json",
        type=Path,
        default=None,
        help="Optional regression receipt output path.",
    )
    return parser.parse_args()


def _load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"missing input file: {path}")
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON payload is not an object: {path}")
    return payload


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n",
        encoding="utf-8",
    )


def _normalize_key(value: str) -> str:
    return "".join(character.lower() for character in value if character.isalnum())


def _join_path(path: tuple[Any, ...]) -> str:
    if not path:
        return ""
    pieces: list[str] = []
    for entry in path:
        if isinstance(entry, int):
            if pieces:
                pieces[-1] += f"[{entry}]"
            else:
                pieces.append(f"[{entry}]")
        else:
            pieces.append(str(entry))
    return ".".join(pieces)


def _record_error(errors: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    errors.append(f"{label}: {message}" if label else message)


def _record_warning(warnings: list[str], path: tuple[Any, ...], message: str) -> None:
    label = _join_path(path)
    warnings.append(f"{label}: {message}" if label else message)


def _iter_nodes(node: Any, path: tuple[Any, ...] = ()) -> Iterable[tuple[tuple[Any, ...], Any]]:
    yield path, node
    if isinstance(node, dict):
        for key, value in node.items():
            yield from _iter_nodes(value, path + (key,))
    elif isinstance(node, list):
        for index, value in enumerate(node):
            yield from _iter_nodes(value, path + (index,))


def _coerce_string(value: Any) -> str | None:
    if isinstance(value, str):
        text = value.strip()
        return text or None
    return None


def _coerce_bool(value: Any) -> bool | None:
    return value if isinstance(value, bool) else None


def _extract_arxiv_ids(payload: dict[str, Any]) -> list[str]:
    ids: list[str] = []
    for _, node in _iter_nodes(payload):
        if isinstance(node, str):
            text = node.strip()
            if text.startswith("arXiv:"):
                text = text.split(":", 1)[1].strip()
            if text in REQUIRED_ARXIV_IDS:
                ids.append(text)
        elif isinstance(node, dict):
            for key in ("arxiv", "arxiv_id", "arxivId", "arxiv_ids", "arxivIds"):
                value = node.get(key)
                if isinstance(value, str):
                    text = value.strip()
                    if text.startswith("arXiv:"):
                        text = text.split(":", 1)[1].strip()
                    if text in REQUIRED_ARXIV_IDS:
                        ids.append(text)
                elif isinstance(value, list):
                    for item in value:
                        text = _coerce_string(item)
                        if text is None:
                            continue
                        if text.startswith("arXiv:"):
                            text = text.split(":", 1)[1].strip()
                        if text in REQUIRED_ARXIV_IDS:
                            ids.append(text)
    return ids


def _find_field(payload: dict[str, Any], aliases: Iterable[str]) -> tuple[str | None, Any | None]:
    alias_list = tuple(aliases)
    for alias in alias_list:
        if alias in payload:
            return alias, payload[alias]
    normalized_aliases = {_normalize_key(alias): alias for alias in alias_list}
    for key, value in payload.items():
        if isinstance(key, str) and _normalize_key(key) in normalized_aliases:
            return key, value
    return None, None


def _find_field_deep(node: Any, aliases: Iterable[str]) -> tuple[tuple[Any, ...] | None, Any | None]:
    alias_list = tuple(aliases)
    normalized_aliases = {_normalize_key(alias): alias for alias in alias_list}
    for path, value in _iter_nodes(node):
        if not path:
            continue
        key = path[-1]
        if not isinstance(key, str):
            continue
        if key in alias_list or _normalize_key(key) in normalized_aliases:
            return path, value
    return None, None


def _check_required_false_flags(payload: dict[str, Any], errors: list[str]) -> None:
    for required_key in REQUIRED_FALSE_FLAGS:
        found_path, found_value = _find_field_deep(payload, (required_key,))
        if found_path is None:
            errors.append(f"missing required flag {required_key!r}")
            continue
        bool_value = _coerce_bool(found_value)
        if bool_value is None:
            _record_error(errors, found_path, f"must be bool, got {type(found_value).__name__}")
            continue
        if bool_value is not False:
            _record_error(errors, found_path, "must be false")


def _check_status_field(payload: dict[str, Any], errors: list[str]) -> None:
    found_path, value = _find_field_deep(payload, ("status",))
    if found_path is None:
        errors.append("missing required status field")
        return
    status = _coerce_string(value)
    if status is None:
        _record_error(errors, found_path, f"must be a non-empty string, got {value!r}")
        return
    if status not in ALLOWED_STATUS_VALUES:
        _record_error(
            errors,
            found_path,
            f"must be one of {sorted(ALLOWED_STATUS_VALUES)!r}, got {status!r}",
        )


def _check_manual_checks(payload: dict[str, Any], errors: list[str]) -> None:
    found_path, value = _find_field_deep(payload, MANUAL_CHECK_KEYS)
    if found_path is None:
        errors.append("missing required manual checks field")
        return
    if isinstance(value, dict):
        if not value:
            _record_error(errors, found_path, "must not be empty")
        return
    if isinstance(value, list):
        if not value:
            _record_error(errors, found_path, "must not be empty")
            return
        return
    if isinstance(value, str):
        if not value.strip():
            _record_error(errors, found_path, "must not be empty")
        return
    _record_error(errors, found_path, f"must be object, list, or string, got {type(value).__name__}")


def _check_arxiv_ids(payload: dict[str, Any], errors: list[str]) -> list[str]:
    found = _extract_arxiv_ids(payload)
    missing = [arxiv_id for arxiv_id in REQUIRED_ARXIV_IDS if arxiv_id not in found]
    if missing:
        errors.append(f"missing required arXiv IDs: {', '.join(missing)}")
    return sorted(set(found))


def _build_result(
    payload: dict[str, Any],
    input_path: Path,
    output_json: Path | None,
) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []

    _check_status_field(payload, errors)
    _check_required_false_flags(payload, errors)
    _check_manual_checks(payload, errors)
    arxiv_ids = _check_arxiv_ids(payload, errors)
    status_path, status_value = _find_field_deep(payload, ("status",))
    manual_checks_present = _find_field_deep(payload, MANUAL_CHECK_KEYS)[0] is not None
    required_false_flags: dict[str, Any] = {}
    for key in REQUIRED_FALSE_FLAGS:
        found_path, found_value = _find_field_deep(payload, (key,))
        if found_path is not None:
            required_false_flags[key] = found_value

    status = OK_STATUS if not errors else ERROR_STATUS
    result = {
        "contract": CONTRACT,
        "status": status,
        "errors": errors,
        "warnings": warnings,
        "inputs": {
            "input_json": str(input_path),
            "output_json": str(output_json) if output_json is not None else None,
        },
        "validation": {
            "arxiv_ids_found": arxiv_ids,
            "required_arxiv_ids": list(REQUIRED_ARXIV_IDS),
            "status_field": status_value if status_path is not None else payload.get("status"),
            "manual_checks_present": manual_checks_present,
            "required_false_flags": required_false_flags,
        },
        "changed_files": [str(input_path)] + ([str(output_json)] if output_json is not None else []),
        "O": "Validate Shahmurov claim intake regression JSON.",
        "R": "Check required arXiv IDs, status gating, promotion flags, and manual-check presence.",
        "C": SCRIPT_NAME,
        "S": "Fail closed when the intake payload violates the recorded regression contract.",
        "L": "Status is ok only when all required intake gates are present and false where required.",
        "P": "FAIL_CLOSED_NS_SHAHMUROV_CLAIM_INTAKE_REGRESSION",
        "G": "No theorem, Clay, or route-superseded claim is inferred by this checker.",
        "F": "This checker only validates empirical intake telemetry and emits a compact status record.",
    }
    return result


def main() -> int:
    try:
        args = _parse_args()
        payload = _load_json(args.input_json)
        result = _build_result(payload, args.input_json, args.output_json)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        result = {
            "contract": CONTRACT,
            "status": ERROR_STATUS,
            "errors": [str(exc)],
            "warnings": [],
            "inputs": {"input_json": None, "output_json": None},
            "validation": {
                "arxiv_ids_found": [],
                "required_arxiv_ids": list(REQUIRED_ARXIV_IDS),
                "status_field": None,
                "manual_checks_present": False,
                "required_false_flags": {},
            },
            "changed_files": [],
            "O": "Validate Shahmurov claim intake regression JSON.",
            "R": "Check required arXiv IDs, status gating, promotion flags, and manual-check presence.",
            "C": SCRIPT_NAME,
            "S": "Fail closed when the intake payload violates the recorded regression contract.",
            "L": "Status is ok only when all required intake gates are present and false where required.",
            "P": "FAIL_CLOSED_NS_SHAHMUROV_CLAIM_INTAKE_REGRESSION",
            "G": "No theorem, Clay, or route-superseded claim is inferred by this checker.",
            "F": "This checker only validates empirical intake telemetry and emits a compact status record.",
        }
        print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
        return 1

    if args.output_json is not None:
        _write_json(args.output_json, result)
    print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
    return 0 if result["status"] == OK_STATUS else 1


if __name__ == "__main__":
    raise SystemExit(main())
