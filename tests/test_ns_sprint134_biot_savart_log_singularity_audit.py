from __future__ import annotations

import csv
import json
import math
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint134_biot_savart_log_singularity_audit"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

SUMMARY_NAME = f"{STEM}_summary.json"
ROWS_JSON_NAME = f"{STEM}_rows.json"
ROWS_CSV_NAME = f"{STEM}_rows.csv"
REPORT_NAME = f"{STEM}.md"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_audit(
    tmp_path: Path,
) -> tuple[subprocess.CompletedProcess[str], Path, dict[str, Any], list[dict[str, Any]], list[dict[str, str]], str]:
    assert SCRIPT.is_file(), f"missing Worker 2 producer script: {SCRIPT.relative_to(REPO_ROOT)}"

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

    text = artifact_text(out_dir, result) if out_dir.exists() else result.stdout + result.stderr
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text

    for name in (SUMMARY_NAME, ROWS_JSON_NAME, ROWS_CSV_NAME, REPORT_NAME):
        path = out_dir / name
        assert path.is_file(), f"missing output {name}\n{text}"
        assert path.stat().st_size > 0, f"empty output {name}"

    summary = load_json_object(out_dir / SUMMARY_NAME)
    rows_json = load_json_rows(out_dir / ROWS_JSON_NAME)
    rows_csv = load_csv_rows(out_dir / ROWS_CSV_NAME)
    return result, out_dir, summary, rows_json, rows_csv, text


def artifact_text(out_dir: Path, result: subprocess.CompletedProcess[str]) -> str:
    paths = sorted(
        path
        for path in out_dir.glob("*")
        if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
    )
    return "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in paths]
    )


def load_json_object(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(payload, dict) and payload, f"{path.name} must be a nonempty JSON object"
    return payload


def load_json_rows(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = payload.get("rows") or payload.get("samples") or payload.get("audit_rows")
    else:
        rows = None
    assert isinstance(rows, list) and rows, f"{path.name} must contain nonempty rows"
    assert all(isinstance(row, dict) for row in rows), f"{path.name} has a non-object row"
    return rows


def load_csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        rows = [dict(row) for row in csv.DictReader(handle)]
    assert rows, f"{path.name} must contain rows"
    return rows


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", " ", str(value).lower()).strip()


def joined_text(*payloads: Any) -> str:
    return "\n".join(
        payload if isinstance(payload, str) else json.dumps(payload, sort_keys=True, default=str)
        for payload in payloads
    )


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = {key.lower() for key in keys}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if str(key).lower() in wanted and isinstance(value, bool):
                values.append(value)
    return values


def clay_guard_flags(payload: Any) -> list[tuple[str, bool]]:
    flags: list[tuple[str, bool]] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if isinstance(value, bool) and "clay" in str(key).lower():
                flags.append((str(key), value))
    return flags


def numeric_values_for_keys(payload: Any, *key_terms: str) -> list[float]:
    values: list[float] = []
    terms = tuple(term.lower() for term in key_terms)
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if not any(term in str(key).lower() for term in terms):
                continue
            try:
                values.append(float(value))
            except (TypeError, ValueError):
                continue
    return values


def latest_ratio(rows: list[dict[str, Any]]) -> float:
    ratio_rows = [
        row
        for row in rows
        if any("ratio" in str(key).lower() for key in row)
        and any(str(value).strip() for value in row.values())
    ]
    assert ratio_rows, "expected rows with ratio values"

    def sort_key(row: dict[str, Any]) -> tuple[float, float]:
        k_values = numeric_values_for_keys(row, "k")
        eps_values = numeric_values_for_keys(row, "epsilon", "one_minus_k", "gap")
        k_score = max(k_values) if k_values else -math.inf
        eps_score = -min(abs(value) for value in eps_values) if eps_values else -math.inf
        return (k_score, eps_score)

    terminal = max(ratio_rows, key=sort_key)
    for key, value in terminal.items():
        normalized_key = str(key).lower()
        if "ratio" not in normalized_key or "error" in normalized_key:
            continue
        try:
            return float(value)
        except (TypeError, ValueError):
            continue
    raise AssertionError(f"terminal ratio row has no numeric non-error ratio: {terminal}")


def assert_mentions_all(text: str, *needles: str) -> None:
    normalized = normalize(text)
    for needle in needles:
        assert normalize(needle) in normalized, f"missing {needle!r} in artifact text"


def test_sprint134_biot_savart_audit_writes_json_csv_and_markdown(tmp_path: Path) -> None:
    _result, out_dir, summary, rows_json, rows_csv, text = run_audit(tmp_path)

    assert out_dir.name == STEM
    assert summary.get("contract", STEM) == STEM
    assert rows_json, text
    assert rows_csv, text
    assert_mentions_all(text, "Biot", "Savart", "axisymmetric", "log")


def test_sprint134_retracts_uniform_no_log_claim_and_preserves_axis_only_scope(tmp_path: Path) -> None:
    _result, _out_dir, summary, rows_json, _rows_csv, text = run_audit(tmp_path)
    payload = {"summary": summary, "rows": rows_json}

    no_log_false_values = bool_values_for_keys(
        payload,
        "uniform_no_log_claim_true",
        "no_log_axisymmetric_biot_savart_uniform",
        "uniform_no_log_claim",
        "uniform_no_log_bound_holds",
    )
    assert no_log_false_values and all(value is False for value in no_log_false_values), json.dumps(payload)

    log_persists_values = bool_values_for_keys(
        payload,
        "standard_log_singularity_persists",
        "log_singularity_persists",
        "standard_calderon_zygmund_log_persists",
    )
    assert log_persists_values and all(value is True for value in log_persists_values), json.dumps(payload)

    axis_only_values = bool_values_for_keys(
        payload,
        "axis_only_scope_true",
        "axis_only_scope",
        "axis_claim_only",
        "near_axis_only",
        "axis_only_extra_r_factor_scope",
        "near_axis_cancellation_not_uniform",
    )
    assert axis_only_values and all(value is True for value in axis_only_values), json.dumps(payload)

    assert_mentions_all(text, "uniform no log", "false", "axis")


def test_sprint134_elliptic_integral_ratios_approach_one_as_k_tends_to_one(tmp_path: Path) -> None:
    _result, _out_dir, summary, rows_json, _rows_csv, text = run_audit(tmp_path)

    ratio_values = numeric_values_for_keys({"summary": summary, "rows": rows_json}, "ratio")
    assert len(ratio_values) >= 3, f"expected multiple ratio samples\n{text}"
    assert any(abs(value - 1.0) < 0.05 for value in ratio_values), ratio_values

    terminal_ratio = latest_ratio(rows_json)
    assert abs(terminal_ratio - 1.0) < 0.02, terminal_ratio
    assert_mentions_all(text, "k", "1")


def test_sprint134_rows_are_nonempty_and_record_log_kernel_asymptotic(tmp_path: Path) -> None:
    _result, _out_dir, summary, rows_json, rows_csv, text = run_audit(tmp_path)

    assert summary.get("row_count", len(rows_json)) >= 1
    assert len(rows_json) >= 1
    assert len(rows_csv) >= 1
    assert len(rows_csv) == len(rows_json)
    assert_mentions_all(text, "K(k)", "log", "4", "sqrt")


def test_sprint134_clay_flags_remain_false(tmp_path: Path) -> None:
    _result, _out_dir, summary, rows_json, _rows_csv, text = run_audit(tmp_path)
    payload = {"summary": summary, "rows": rows_json}

    full_clay_flags = bool_values_for_keys(payload, "full_clay_ns_solved", "full_clay_solved")
    promotion_flags = bool_values_for_keys(
        payload,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    assert full_clay_flags and all(value is False for value in full_clay_flags), json.dumps(payload)
    assert promotion_flags and all(value is False for value in promotion_flags), json.dumps(payload)

    for key, value in clay_guard_flags(payload):
        assert value is False, f"Clay guard flag unexpectedly true: {(key, value)}"
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
