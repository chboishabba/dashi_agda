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

ROUTE_STEM = "ns_sprint139_barrier_route_fork_classifier"
KERNEL_STEM = "ns_sprint139_localized_kernel_sign_sampler"

ROUTE_SCRIPT = SCRIPT_DIR / f"{ROUTE_STEM}.py"
KERNEL_SCRIPT = SCRIPT_DIR / f"{KERNEL_STEM}.py"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)

OPEN_TERMS = {"blocked", "blocker", "fail_open", "gap", "open", "unresolved"}
FAIL_CLOSED_TERMS = {"fail_closed", "not_promoted", "obstructed", "rejected"}
COMPLETED_TERMS = {"closed", "complete", "completed", "proved", "proven", "resolved"}
REQUIRED_BLOCKER_FIELDS = (
    "blocker_id",
    "blocker_status",
    "blocked_claim",
    "missing_input",
)


def run_sprint139_script(
    tmp_path: Path,
    stem: str,
) -> tuple[subprocess.CompletedProcess[str], list[Any], list[dict[str, Any]], str]:
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

    assert out_dir.is_dir(), artifact_text
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    return result, payloads, rows, artifact_text


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


def text_of(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def key_matches(key: str, *names: str) -> bool:
    folded = normalize(key)
    return any(folded == normalize(name) for name in names)


def bool_values_for_keys(payload: Any, *names: str) -> list[bool]:
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if key_matches(str(key), *names) and isinstance(value, bool):
                values.append(value)
    return values


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in walk(payloads):
        if isinstance(item, dict) and any(
            key in item
            for key in (
                "row_id",
                "route_id",
                "kernel_average",
            )
        ):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def rows_with_terms(rows: list[dict[str, Any]], *terms: str) -> list[dict[str, Any]]:
    wanted = tuple(normalize(term) for term in terms)
    return [row for row in rows if all(term in text_of(row) for term in wanted)]


def assert_false_flag(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing false flag for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_no_clay_solution_or_promotion(payloads: list[Any], text: str) -> None:
    assert_false_flag(payloads, text, "full_clay_ns_solved", "full_clay_solved")
    assert_false_flag(
        payloads,
        text,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_no_accidental_completed_or_proved_flags(payloads: list[Any], text: str) -> None:
    completed_values = bool_values_for_keys(
        payloads,
        "complete",
        "completed",
        "closed",
        "claim_closed",
        "proved",
        "proven",
        "is_proved",
        "is_proven",
    )
    assert completed_values, f"missing explicit completion/proof flags\n{text}"
    assert all(value is False for value in completed_values), completed_values

    status_text = text_of(payloads)
    assert "proved_true" not in status_text
    assert "proven_true" not in status_text
    assert "completed_true" not in status_text


def assert_blocker_fields(rows: list[dict[str, Any]], text: str) -> None:
    blocker_rows = rows_with_terms(rows, "blocker")
    assert blocker_rows, f"missing blocker rows\n{text}"

    for row in blocker_rows:
        row_keys = {normalize(key) for key in row}
        missing = [
            field
            for field in REQUIRED_BLOCKER_FIELDS
            if normalize(field) not in row_keys
            and not any(normalize(field) in key for key in row_keys)
        ]
        assert not missing, f"missing blocker fields {missing} in {row}"

    blocker_text = text_of(blocker_rows)
    assert any(term in blocker_text for term in OPEN_TERMS), blocker_text
    for row in blocker_rows:
        for key, value in row.items():
            if normalize(key) in {
                "closed",
                "complete",
                "completed",
                "proved",
                "proven",
                "claim_closed",
                "claim_proved",
                "claim_proven",
            }:
                assert str(value).lower() in {"false", "0", ""}, row


def test_sprint139_route_classifier_records_fail_closed_and_open_route_decisions(
    tmp_path: Path,
) -> None:
    result, payloads, rows, text = run_sprint139_script(tmp_path, ROUTE_STEM)
    combined = text_of([payloads, rows, text])

    assert result.returncode in {0, 1}, text
    assert ROUTE_STEM in combined
    assert rows_with_terms(rows, "fail", "closed") or any(
        term in combined for term in FAIL_CLOSED_TERMS
    ), text
    assert rows_with_terms(rows, "open") or any(term in combined for term in OPEN_TERMS), text
    assert rows_with_terms(rows, "route"), text

    assert_blocker_fields(rows, text)
    assert_no_clay_solution_or_promotion(payloads, text)
    assert_no_accidental_completed_or_proved_flags(payloads, text)


def test_sprint139_localized_kernel_sampler_records_open_blocker_rows(
    tmp_path: Path,
) -> None:
    result, payloads, rows, text = run_sprint139_script(tmp_path, KERNEL_STEM)
    combined = text_of([payloads, rows, text])

    assert result.returncode in {0, 1}, text
    assert KERNEL_STEM in combined
    assert "localized_kernel" in combined or rows_with_terms(rows, "localized", "kernel")
    assert "sign" in combined
    assert rows_with_terms(rows, "kernel"), text

    assert_blocker_fields(rows, text)
    assert_no_clay_solution_or_promotion(payloads, text)
    assert_no_accidental_completed_or_proved_flags(payloads, text)
