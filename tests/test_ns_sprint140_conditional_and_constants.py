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

CONDITIONAL_STEM = "ns_sprint140_conditional_barrier_assembly"
CONSTANT_LEDGER_STEM = "ns_sprint140_constant_compatibility_ledger"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
)

PROOF_TRUE_PATTERNS = (
    re.compile(r'"(?:proved|proven|proof|global_proof|unconditional_proof)"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\b(?:proved|proven|global[_\s-]*proof|unconditional[_\s-]*proof)\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_sprint140_script(
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

    assert result.returncode == 0, artifact_text
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
            normalize(key) in {"row_id", "assumption_name", "assumption_id", "claim_id", "ledger_id"}
            for key in item
        ):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def assert_all_false(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing boolean values for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_all_true(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing boolean values for {names}\n{text}"
    assert all(value is True for value in values), values


def assert_terms(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing}\n{text}"


def assert_named_assumptions(rows: list[dict[str, Any]], text: str) -> None:
    assumption_rows = [
        row
        for row in rows
        if "assumption" in text_of(row)
        or any("assumption" in normalize(key) for key in row)
    ]
    assert assumption_rows, f"missing named assumption rows\n{text}"
    for row in assumption_rows:
        keys = {normalize(key) for key in row}
        assert any(
            key in keys for key in {"assumption_name", "assumption_id", "name", "assumption"}
        ), row
        assert any(str(value).strip() for value in row.values()), row


def assert_fail_closed_absent_compatibility_inputs(text: str) -> None:
    compact = normalize(text)
    assert "compatibility" in compact, text
    assert "input" in compact or "inputs" in compact, text
    assert any(term in compact for term in {"absent", "missing", "unavailable"}), text
    assert any(term in compact for term in {"fail_closed", "fail_closed"}), text


def assert_no_clay_solution_or_promotion(payloads: list[Any], text: str) -> None:
    assert_all_false(payloads, text, "full_clay_ns_solved", "full_clay_solved")
    assert_all_false(
        payloads,
        text,
        "clayNavierStokesPromoted",
        "clay_navier_stokes_promoted",
        "clay_promoted",
    )
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_no_accidental_true_proof_flags(payloads: list[Any], text: str) -> None:
    assert_all_false(
        payloads,
        text,
        "global_proof",
        "global_proved",
        "global_proven",
        "unconditional_proof",
        "unconditional_proved",
        "unconditional_proven",
    )
    for pattern in PROOF_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_conditional_barrier_assembly_is_conditional_and_fail_closed(
    tmp_path: Path,
) -> None:
    _, payloads, rows, text = run_sprint140_script(tmp_path, CONDITIONAL_STEM)
    combined = "\n".join([text, text_of(payloads), text_of(rows)])

    assert_terms(combined, CONDITIONAL_STEM, "conditional", "barrier", "not", "full", "clay")
    assert_named_assumptions(rows, text)
    assert_fail_closed_absent_compatibility_inputs(combined)
    assert_all_true(payloads, text, "conditional_not_full_clay")
    assert_no_accidental_true_proof_flags(payloads, text)
    assert_no_clay_solution_or_promotion(payloads, text)


def test_constant_compatibility_ledger_records_absent_inputs_without_promotion(
    tmp_path: Path,
) -> None:
    _, payloads, rows, text = run_sprint140_script(tmp_path, CONSTANT_LEDGER_STEM)
    combined = "\n".join([text, text_of(payloads), text_of(rows)])

    assert_terms(combined, CONSTANT_LEDGER_STEM, "constant", "compatibility", "ledger")
    assert_named_assumptions(rows, text)
    assert_fail_closed_absent_compatibility_inputs(combined)
    assert_no_accidental_true_proof_flags(payloads, text)
    assert_no_clay_solution_or_promotion(payloads, text)
