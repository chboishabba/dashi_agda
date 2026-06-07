from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint135_hou_luo_blowup_gate_classifier"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

EXPECTED_GATE_TERMS = {
    "corrected_axisymmetric_equations",
    "swirl_circulation_maximum_principle",
    "boundary_annulus_u1_bound",
    "log_biot_savart_growth",
    "source_vs_viscosity_model",
    "large_re_transient_control",
    "marginal_beta_zero_case",
    "bkm_blowup_alignment",
}

OPEN_STATUSES = {
    "open",
    "blocked",
    "gap",
    "unknown",
    "pending",
    "live",
    "open_live_candidate",
    "not_closed",
    "unresolved",
}

CLOSED_STATUSES = {
    "closed",
    "proved",
    "proven",
    "complete",
    "resolved",
    "unconditional",
    "promoted",
}

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_classifier(
    tmp_path: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, str]], str]:
    assert SCRIPT.is_file(), f"missing Worker 2 script: {SCRIPT.relative_to(REPO_ROOT)}"

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

    text = collect_artifact_text(out_dir, result)
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in json_paths + csv_paths + md_paths)

    json_payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    summary = merge_json_objects(json_payloads)
    rows_json = flatten_rows(json_payloads)
    rows_csv = load_csv_rows(csv_paths)
    assert summary, "expected at least one summary JSON object"
    assert rows_json or rows_csv, "expected JSON or CSV gate rows"
    return summary, rows_json, rows_csv, text


def collect_artifact_text(out_dir: Path, result: subprocess.CompletedProcess[str]) -> str:
    paths: list[Path] = []
    if out_dir.exists():
        paths = sorted(
            path
            for path in out_dir.glob("*")
            if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
        )
    return "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in paths]
    )


def merge_json_objects(payloads: list[Any]) -> dict[str, Any]:
    merged: dict[str, Any] = {}
    for payload in payloads:
        if isinstance(payload, dict):
            merged.update(payload)
    return merged


def flatten_rows(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        rows: list[dict[str, Any]] = []
        for key in (
            "gates",
            "gate_rows",
            "rows",
            "result_rows",
            "gap_rows",
            "classifier_rows",
            "proof_gates",
            "blowup_gates",
        ):
            child = value.get(key)
            if isinstance(child, list):
                rows.extend(row for row in child if isinstance(row, dict))
        if looks_like_gate_row(value):
            rows.append(value)
        for child in value.values():
            rows.extend(flatten_rows(child))
        return dedupe_rows(rows)
    if isinstance(value, list):
        return dedupe_rows([row for child in value for row in flatten_rows(child)])
    return []


def looks_like_gate_row(value: dict[str, Any]) -> bool:
    if set(value) == {"key", "value"}:
        return False
    row_keys = {
        "gate",
        "gate_id",
        "gate_name",
        "name",
        "lemma",
        "status",
        "classification",
        "closure_status",
    }
    return bool(row_keys.intersection(value))


def dedupe_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[str] = set()
    unique: list[dict[str, Any]] = []
    for row in rows:
        key = json.dumps(row, sort_keys=True, default=str)
        if key not in seen:
            seen.add(key)
            unique.append(row)
    return unique


def load_csv_rows(paths: Iterable[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def norm(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def compact_text(value: Any) -> str:
    return norm(json.dumps(value, sort_keys=True, default=str))


def values_for_key_fragments(payload: Any, *fragments: str) -> list[tuple[str, Any]]:
    found: list[tuple[str, Any]] = []
    wanted = tuple(fragment.lower() for fragment in fragments)
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if any(fragment in str(key).lower() for fragment in wanted):
                found.append((str(key), value))
    return found


def bool_values_for_key_fragments(payload: Any, *fragments: str) -> list[tuple[str, bool]]:
    return [
        (key, value)
        for key, value in values_for_key_fragments(payload, *fragments)
        if isinstance(value, bool)
    ]


def row_status(row: dict[str, Any]) -> str:
    for key in ("status", "classification", "closure_status", "gate_status", "state"):
        value = row.get(key)
        if value is not None:
            return norm(value)
    return compact_text(row)


def gate_identity(row: dict[str, Any]) -> str:
    values: list[Any] = []
    for key in ("gate_id", "gate", "gate_name", "name", "lemma", "id"):
        value = row.get(key)
        if value is not None:
            values.append(value)
    if not values:
        values.append(row)
    return compact_text(values)


def all_rows(rows_json: list[dict[str, Any]], rows_csv: list[dict[str, str]]) -> list[dict[str, Any]]:
    return rows_json + [dict(row) for row in rows_csv]


def test_sprint135_hou_luo_blowup_gate_classifier_writes_json_csv_markdown(
    tmp_path: Path,
) -> None:
    summary, rows_json, rows_csv, text = run_classifier(tmp_path)

    assert summary.get("contract", STEM) == STEM
    assert rows_json, text
    assert rows_csv, text
    assert "hou" in text.lower()
    assert "luo" in text.lower()
    assert "blowup" in text.lower()


def test_sprint135_records_at_least_eight_key_blowup_gates(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_classifier(tmp_path)
    rows = all_rows(rows_json, rows_csv)

    assert len(rows) >= 8, json.dumps(rows, indent=2, sort_keys=True, default=str)
    gate_text = "\n".join(gate_identity(row) for row in rows)
    missing = [gate for gate in EXPECTED_GATE_TERMS if norm(gate) not in gate_text]
    assert not missing, f"missing gates {missing}\n{json.dumps(summary, indent=2, sort_keys=True)}\n{text}"


def test_sprint135_keeps_blowup_and_regularity_paths_unclosed(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_classifier(tmp_path)

    blowup_flags = bool_values_for_key_fragments(summary, "blowup_path_closed")
    regularity_flags = bool_values_for_key_fragments(summary, "regularity_path_closed")
    assert blowup_flags and all(value is False for _key, value in blowup_flags), json.dumps(summary)
    assert regularity_flags and all(value is False for _key, value in regularity_flags), json.dumps(summary)

    route_values = values_for_key_fragments(summary, "route")
    route_text = compact_text(route_values + [summary, rows_json, rows_csv, text])
    assert "open_live_candidate" in route_text


def test_sprint135_all_gates_are_open_or_blocked_not_closed(tmp_path: Path) -> None:
    _summary, rows_json, rows_csv, _text = run_classifier(tmp_path)
    rows = all_rows(rows_json, rows_csv)

    assert rows
    for row in rows:
        status = row_status(row)
        assert any(open_status in status for open_status in OPEN_STATUSES), row
        assert not any(closed_status in status for closed_status in CLOSED_STATUSES), row


def test_sprint135_clay_flags_remain_false(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_classifier(tmp_path)

    clay_flags = bool_values_for_key_fragments(
        [summary, rows_json, rows_csv],
        "clay",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
    )
    assert clay_flags, "expected explicit Clay guard flags"
    for key, value in clay_flags:
        if key in {"clay_absent", "clay_not_promoted", "no_clay_promotion_detected"}:
            continue
        assert value is False, f"Clay guard flag unexpectedly true: {(key, value)}"
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
