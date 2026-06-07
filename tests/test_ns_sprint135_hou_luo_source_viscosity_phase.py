from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint135_hou_luo_source_viscosity_phase"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

SUMMARY_NAME = f"{STEM}_summary.json"
ROWS_JSON_NAME = f"{STEM}_rows.json"
ROWS_CSV_NAME = f"{STEM}_rows.csv"
REPORT_NAME = f"{STEM}.md"

SPRINT134_INPUT_TERMS = (
    "ns_sprint134_axisymmetric_equation_correction",
    "ns_sprint134_biot_savart_log_singularity_audit",
    "ns_sprint134_hou_luo_retraction_status",
)

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_phase_audit(
    tmp_path: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, str]], str]:
    assert SCRIPT.is_file(), f"missing Worker 1 producer script: {SCRIPT.relative_to(REPO_ROOT)}"

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
    rows_json = load_rows_json(out_dir / ROWS_JSON_NAME)
    rows_csv = load_csv_rows(out_dir / ROWS_CSV_NAME)
    return summary, rows_json, rows_csv, text


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


def load_rows_json(path: Path) -> list[dict[str, Any]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(payload, list):
        rows = payload
    elif isinstance(payload, dict):
        rows = payload.get("rows") or payload.get("phase_rows") or payload.get("audit_rows")
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


def joined_text(*payloads: Any) -> str:
    return "\n".join(
        payload if isinstance(payload, str) else json.dumps(payload, sort_keys=True, default=str)
        for payload in payloads
    )


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", " ", str(value).lower()).strip()


def compact(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


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


def bool_values_for_key_fragments(payload: Any, *fragments: str) -> list[tuple[str, bool]]:
    wanted = tuple(fragment.lower() for fragment in fragments)
    found: list[tuple[str, bool]] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if isinstance(value, bool) and any(fragment in str(key).lower() for fragment in wanted):
                found.append((str(key), value))
    return found


def text_mentions_all(text: str, *terms: str) -> bool:
    haystack = normalize(text)
    return all(normalize(term) in haystack for term in terms)


def row_text(row: dict[str, Any]) -> str:
    return joined_text(row).lower()


def row_compact_text(row: dict[str, Any]) -> str:
    return compact(joined_text(row))


def numeric_values_for_key_terms(row: dict[str, Any], *terms: str) -> list[float]:
    values: list[float] = []
    wanted = tuple(term.lower() for term in terms)
    for key, value in row.items():
        if not any(term in str(key).lower() for term in wanted):
            continue
        try:
            values.append(float(value))
        except (TypeError, ValueError):
            continue
    return values


def row_claims_source_beats_viscosity(row: dict[str, Any]) -> bool:
    text = row_text(row)
    compact_text = row_compact_text(row)
    if "log" not in text or "gronwall" not in text:
        return False
    source_terms = ("source", "forcing", "gronwall")
    viscosity_terms = ("viscos", "damping", "diffus")
    beats_terms = ("beat", "dominat", "outgrow", "exceed", "wins")
    if any(term not in text for term in source_terms[:1]):
        return False
    if not any(term in text for term in viscosity_terms):
        return False
    if any(term in text for term in beats_terms):
        return True

    verdict = str(row.get("phase") or row.get("verdict") or row.get("comparison") or row.get("status", ""))
    if compact(verdict) in {"source_beats_viscosity", "source_dominates_viscosity", "source_outgrows_viscosity"}:
        return True

    ratio_values = numeric_values_for_key_terms(row, "source_to_viscosity", "source_over_viscosity")
    return bool(ratio_values and max(ratio_values) > 1.0)


def row_proves_blowup(row: dict[str, Any]) -> bool:
    text = row_compact_text(row)
    if "blowup" not in text and "bkm_divergence" not in text:
        return False
    proof_true_keys = (
        "blowup_proved",
        "proves_blowup",
        "bkm_blowup_proved",
        "finite_time_blowup_proved",
    )
    for key in proof_true_keys:
        value = row.get(key)
        if value is True or (isinstance(value, str) and value.lower() == "true"):
            return True
    proof_phrases = (
        "blowup_proved",
        "proved_blowup",
        "finite_time_blowup_is_proved",
        "bkm_divergence_proved",
    )
    return any(phrase in text for phrase in proof_phrases)


def test_sprint135_phase_audit_writes_json_csv_and_markdown(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_phase_audit(tmp_path)

    assert summary.get("contract", STEM) == STEM
    assert rows_json, text
    assert rows_csv, text
    assert text_mentions_all(text, "Hou", "Luo", "source", "viscosity")


def test_sprint135_acknowledges_sprint134_correction_inputs(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_phase_audit(tmp_path)
    payload_text = joined_text(summary, rows_json, rows_csv, text).lower()

    assert "sprint134" in payload_text
    for term in SPRINT134_INPUT_TERMS:
        assert term in payload_text, f"missing Sprint134 dependency {term}"
    assert text_mentions_all(payload_text, "axisymmetric", "equation", "correction")
    assert text_mentions_all(payload_text, "biot", "savart", "log")
    assert text_mentions_all(payload_text, "retraction", "status")


def test_sprint135_retracts_polynomial_obstruction_model_and_keeps_route_live(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_phase_audit(tmp_path)
    payload = {"summary": summary, "rows_json": rows_json, "rows_csv": rows_csv}
    payload_text = joined_text(payload, text)
    payload_norm = normalize(payload_text)
    payload_compact = compact(payload_text)

    polynomial_retraction_flags = bool_values_for_key_fragments(payload, "polynomial", "obstruction", "retract")
    assert any(value is True for key, value in polynomial_retraction_flags if "retract" in key.lower()), payload_text

    assert "polynomial obstruction" in payload_norm
    assert "retract" in payload_norm or "retracted" in payload_norm
    assert "open_live_candidate" in payload_compact

    route_flags = bool_values_for_keys(
        payload,
        "hou_luo_route_open",
        "hou_luo_axisymmetric_ns_route_open",
        "open_live_candidate",
    )
    assert not route_flags or all(value is True for value in route_flags), payload_text


def test_sprint135_has_log_gronwall_phase_where_source_beats_viscosity(tmp_path: Path) -> None:
    _summary, rows_json, rows_csv, text = run_phase_audit(tmp_path)
    all_rows: list[dict[str, Any]] = rows_json + rows_csv

    source_beats_rows = [row for row in all_rows if row_claims_source_beats_viscosity(row)]
    assert source_beats_rows, joined_text(all_rows, text)


def test_sprint135_keeps_clay_flags_false_and_makes_no_blowup_proof_claim(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_phase_audit(tmp_path)
    payload = {"summary": summary, "rows_json": rows_json, "rows_csv": rows_csv}

    clay_flags = [
        (key, value)
        for item in walk(payload)
        if isinstance(item, dict)
        for key, value in item.items()
        if isinstance(value, bool) and "clay" in str(key).lower()
    ]
    assert clay_flags, joined_text(payload, text)
    for key, value in clay_flags:
        if str(key) in {"clay_absent", "clay_not_promoted", "no_clay_promotion_detected"}:
            continue
        assert value is False, f"Clay guard flag unexpectedly true: {(key, value)}"

    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern

    all_rows = rows_json + rows_csv
    assert not any(row_proves_blowup(row) for row in all_rows), joined_text(all_rows, text)
    assert "blowup proved" not in normalize(text)
    assert "proved blowup" not in normalize(text)
