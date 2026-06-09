from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint151_width_ode_extraction"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint151LocalizedEnstrophyIdentityReceipt.agda"
)

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
FALSE_FLAG_NAMES = {
    "width_ode_extracted_from_ns",
    "bkm_finite",
    "full_clay_ns_solved",
}
AGDA_FALSE_ASSIGNMENTS = {
    "LocalizedEnstrophyIdentityAtScaleDelta",
    "LocalizedEnstrophyIdentityAtScaleDeltaProved",
    "ModelValidityForWidthODE",
    "ModelValidityForWidthODEProved",
    "ScalingCouplingConsistency",
    "ScalingCouplingConsistencyProved",
    "SymmetricHouLuoBKMFinite",
    "SymmetricHouLuoBKMFiniteProved",
    "full_clay_ns_solved",
    "clayNavierStokesPromoted",
}
TRUE_COMPLETION_PATTERNS = (
    re.compile(
        r'"(?:width_ode_extracted_from_ns|bkm_finite|full_clay_ns_solved|'
        r'clay_navier_stokes_promoted|promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:LocalizedEnstrophyIdentityAtScaleDelta|"
        r"LocalizedEnstrophyIdentityAtScaleDeltaProved|"
        r"ModelValidityForWidthODE|ModelValidityForWidthODEProved|"
        r"ScalingCouplingConsistency|ScalingCouplingConsistencyProved|"
        r"SymmetricHouLuoBKMFinite|SymmetricHouLuoBKMFiniteProved|full_clay_ns_solved|"
        r"clayNavierStokesPromoted|promotionAllowed)\s*=\s*true\b"
    ),
)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def compact(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def as_float(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, int | float):
        return float(value)
    if isinstance(value, str):
        try:
            return float(value)
        except ValueError:
            return None
    return None


def sign_value(value: Any) -> int | None:
    numeric = as_float(value)
    if numeric is not None:
        if numeric > 0:
            return 1
        if numeric < 0:
            return -1
        return 0

    text = normalize(value)
    if text in {"positive", "pos", "plus", "greater_than_zero", "gt_zero"}:
        return 1
    if text in {"negative", "neg", "minus", "less_than_zero", "lt_zero"}:
        return -1
    if text in {"zero", "neutral", "equilibrium", "balanced", "equal_zero", "eq_zero"}:
        return 0
    return None


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_markers = {
        "row_id",
        "case_id",
        "scenario_id",
        "regime_id",
        "equilibrium_case",
        "status",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_markers for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(values: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    found: list[bool] = []
    for item in walk(values):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(value)
                if parsed is not None:
                    found.append(parsed)
    return found


def assert_control_card_present(payloads: list[Any], text: str) -> None:
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        if CONTROL_CARD_KEYS.issubset({str(key) for key in item}):
            return
        card = item.get("control_card") or item.get("control-card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
    normalized_text = normalize(text)
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalized_text]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def run_width_ode_extraction(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    if not SCRIPT.is_file():
        pytest.skip(f"{SCRIPT.relative_to(REPO_ROOT)} is not present yet")

    out_dir = tmp_path / STEM
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(REPO_ROOT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    artifact_paths = sorted(out_dir.glob("*")) if out_dir.exists() else []
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )

    assert result.returncode == 0, text
    assert out_dir.is_dir(), text
    assert json_paths, text
    assert csv_paths, text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, text
    return payloads, rows, text, out_dir


def row_has_case(row: dict[str, Any], *needles: str) -> bool:
    row_text = compact(row)
    return all(normalize(needle) in row_text for needle in needles)


def row_signs(row: dict[str, Any]) -> list[int]:
    signish_keys = (
        "sign",
        "rhs",
        "derivative",
        "drift",
        "width_dot",
        "ode_value",
        "linearized_value",
        "residual",
    )
    signs: list[int] = []
    for key, value in row.items():
        key_text = normalize(key)
        if any(marker in key_text for marker in signish_keys):
            parsed = sign_value(value)
            if parsed is not None:
                signs.append(parsed)
    return signs


def assert_equilibrium_sign_behavior(rows: list[dict[str, Any]], text: str) -> None:
    below_rows = [row for row in rows if row_has_case(row, "below", "equilibrium")]
    above_rows = [row for row in rows if row_has_case(row, "above", "equilibrium")]
    equilibrium_rows = [
        row
        for row in rows
        if row_has_case(row, "equilibrium")
        and not row_has_case(row, "below")
        and not row_has_case(row, "above")
    ]

    assert below_rows, f"missing below-equilibrium sign row\n{text}"
    assert above_rows, f"missing above-equilibrium sign row\n{text}"
    assert any(any(sign > 0 for sign in row_signs(row)) for row in below_rows), below_rows
    assert any(any(sign < 0 for sign in row_signs(row)) for row in above_rows), above_rows
    if equilibrium_rows:
        assert any(any(sign == 0 for sign in row_signs(row)) for row in equilibrium_rows), (
            equilibrium_rows
        )


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def test_width_ode_extraction_emits_equilibrium_signs_and_fail_closed_flags(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_width_ode_extraction(tmp_path)
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert out_dir.name == STEM
    assert "width" in combined
    assert "ode" in combined
    assert "equilibrium" in combined
    assert_control_card_present(payloads, text)
    assert_equilibrium_sign_behavior(rows, text)

    for name in FALSE_FLAG_NAMES:
        values = bool_values_for_keys([payloads, rows], name)
        assert values, f"missing false flag {name}\n{text}"
        assert all(value is False for value in values), (name, values)

    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_localized_enstrophy_identity_receipt_imports_sprint149_and_stays_fail_closed() -> None:
    if not RECEIPT.is_file():
        pytest.skip(f"{RECEIPT.relative_to(REPO_ROOT)} is not present yet")

    text = RECEIPT.read_text(encoding="utf-8")
    normalized = normalize(text)
    required_terms = [
        "NSSprint151LocalizedEnstrophyIdentityReceipt",
        "LocalizedEnstrophyIdentityAtScaleDelta",
        "widthEquilibriumModelSupport",
        "subcriticalWidthODESupport",
        "ModelValidityForWidthODE",
        "NSSprint149ScalingConsistencyGateReceipt",
        "fail",
        "closed",
    ]
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    for name in AGDA_FALSE_ASSIGNMENTS:
        assert agda_bool_assignment(text, name, False), name
    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern

    result = subprocess.run(
        ["agda", str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
