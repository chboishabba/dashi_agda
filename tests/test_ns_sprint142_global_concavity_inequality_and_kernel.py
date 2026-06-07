from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

CONCAVITY_STEM = "ns_sprint142_global_concavity_inequality"
KERNEL_STEM = "ns_sprint142_kernel_sign_stress_sampler"

TRUE_SOLUTION_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)

TRUE_CLOSURE_PATTERNS = (
    re.compile(r'"global_concavity_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_barrier_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bglobal[_\s-]*concavity[_\s-]*proved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bglobal[_\s-]*barrier[_\s-]*closed\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bsimultaneous[_\s-]*(?:theorem|constants?)[_\s-]*(?:and|with)?[_\s-]*(?:constants?|theorem)?\b\s*[:=]\s*true\b", re.IGNORECASE),
)

ROW_KEYS = {
    "row_id",
    "id",
    "name",
    "claim_id",
    "inequality_id",
    "sample_id",
    "case_id",
    "scenario_id",
    "obstruction_id",
    "blocker_id",
}


def run_sprint142_script(tmp_path: Path, stem: str) -> tuple[list[Any], list[dict[str, Any]], str]:
    script = SCRIPT_DIR / f"{stem}.py"
    assert script.is_file(), "missing " + str(script.relative_to(REPO_ROOT))

    out_dir = tmp_path / stem
    result = subprocess.run(
        [
            sys.executable,
            str(script),
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

    paths = sorted(out_dir.glob("*")) if out_dir.exists() else []
    json_paths = [path for path in paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in paths if path.suffix.lower() == ".md"]
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [
            path.read_text(encoding="utf-8", errors="replace")
            for path in [*json_paths, *csv_paths, *md_paths]
        ]
    )

    assert result.returncode in {0, 1}, artifact_text
    assert out_dir.is_dir(), artifact_text
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, artifact_text
    return payloads, rows, artifact_text


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


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    normalized_row_keys = {normalize(key) for key in ROW_KEYS}
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in normalized_row_keys for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(payloads: list[Any], *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(payloads):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted and isinstance(value, bool):
                values.append(value)
    return values


def rows_with_terms(rows: list[dict[str, Any]], *terms: str) -> list[dict[str, Any]]:
    wanted = tuple(normalize(term) for term in terms)
    return [row for row in rows if all(term in compact(row) for term in wanted)]


def assert_terms(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing}\n{text}"


def assert_false_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing explicit false flags for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_named_rows(rows: list[dict[str, Any]], text: str) -> None:
    named_rows = [
        row
        for row in rows
        if any(normalize(key) in {normalize(item) for item in ROW_KEYS} for key in row)
    ]
    assert named_rows, f"missing named rows\n{text}"
    for row in named_rows:
        assert any(str(value).strip() for value in row.values()), row


def assert_local_support_and_nonlocal_adverse_obstruction(
    rows: list[dict[str, Any]],
    text: str,
) -> None:
    local_support_rows = rows_with_terms(rows, "local", "support")
    assert local_support_rows, f"missing local support rows\n{text}"

    obstruction_rows = [
        row
        for row in rows
        if "obstruction" in compact(row)
        and (
            "nonlocal" in compact(row)
            or "adverse" in compact(row)
            or "wrong_sign" in compact(row)
            or "sign_indefinite" in compact(row)
            or "boundary" in compact(row)
            or "annular" in compact(row)
        )
    ]
    assert obstruction_rows, f"missing nonlocal/adverse obstruction rows\n{text}"


def assert_absent_simultaneous_theorem_and_constants(text: str) -> None:
    compact_text = normalize(text)
    assert "theorem" in compact_text, text
    assert "constant" in compact_text or "constants" in compact_text, text
    assert any(term in compact_text for term in {"absent", "missing", "unavailable", "not_available"}), text
    assert not any(pattern.search(text) for pattern in TRUE_CLOSURE_PATTERNS), text


def assert_no_solution_or_promotion(payloads: list[Any], text: str) -> None:
    for name in ("full_clay_ns_solved", "clay_navier_stokes_promoted"):
        values = bool_values_for_keys(payloads, name)
        if values:
            assert all(value is False for value in values), values
    for pattern in TRUE_SOLUTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_sprint142_contract(stem: str, payloads: list[Any], rows: list[dict[str, Any]], text: str) -> None:
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert_terms(combined, stem, "global", "concavity")
    assert_named_rows(rows, text)
    assert_local_support_and_nonlocal_adverse_obstruction(rows, text)
    assert_absent_simultaneous_theorem_and_constants(combined)
    assert_false_flags(payloads, text, "global_concavity_proved")
    assert_false_flags(payloads, text, "global_barrier_closed")
    assert_no_solution_or_promotion(payloads, text)


def test_global_concavity_inequality_records_obstruction_without_promotion(
    tmp_path: Path,
) -> None:
    payloads, rows, text = run_sprint142_script(tmp_path, CONCAVITY_STEM)
    assert_sprint142_contract(CONCAVITY_STEM, payloads, rows, text)
    assert_terms("\n".join([text, compact(rows)]), "inequality")


def test_kernel_sign_stress_sampler_records_adverse_nonlocal_samples_without_promotion(
    tmp_path: Path,
) -> None:
    payloads, rows, text = run_sprint142_script(tmp_path, KERNEL_STEM)
    assert_sprint142_contract(KERNEL_STEM, payloads, rows, text)
    assert_terms("\n".join([text, compact(rows)]), "kernel", "sign", "stress")
