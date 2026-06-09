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
STEM = "ns_sprint144_nonlocal_source_zero_number_failure"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT144_MODULE = (
    "DASHI.Physics.Closure.NSSprint144CoupledZeroNumberObstructionReceipt"
)
SPRINT144_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint144CoupledZeroNumberObstructionReceipt.agda"
)

ZERO_NUMBER_SYMBOL = "CoupledAxisymmetricZeroNumberForVBarrier"

TRUE_COMPLETION_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"coupled_zero_number_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"comparison_envelope_exists"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
    re.compile(r"\bglobal[_\s-]*proof[_\s-]*(?:closed|proved|proven)\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_nonlocal_zero_number_failure(
    tmp_path: Path,
) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

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

    artifact_paths = (
        sorted(
            path
            for path in out_dir.glob("*")
            if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
        )
        if out_dir.exists()
        else []
    )
    json_paths = [path for path in artifact_paths if path.suffix.lower() == ".json"]
    csv_paths = [path for path in artifact_paths if path.suffix.lower() == ".csv"]
    md_paths = [path for path in artifact_paths if path.suffix.lower() == ".md"]
    artifact_text = "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in artifact_paths]
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
    return payloads, rows, artifact_text, out_dir


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


def compact_text(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_keys = {
        "artifact_id",
        "claim_id",
        "invariant_id",
        "ledger_id",
        "obstruction_id",
        "row_id",
        "route_decision",
        "status",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_keys for key in item):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_exact_keys(payload: Any, *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted and isinstance(value, bool):
                values.append(value)
    return values


def bool_values_for_key_terms(payload: Any, *terms: str) -> list[bool]:
    wanted = [normalize(term) for term in terms]
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_text = normalize(key)
            if isinstance(value, bool) and all(term in key_text for term in wanted):
                values.append(value)
    return values


def rows_mentioning(value: Any, *terms: str) -> list[dict[str, Any]]:
    wanted = [normalize(term) for term in terms]
    rows: list[dict[str, Any]] = []
    for item in walk(value):
        if not isinstance(item, dict):
            continue
        text = compact_text(item)
        if all(term in text for term in wanted):
            rows.append(item)
    return rows


def assert_text_has_all(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing}\n{text}"


def assert_any_false(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_exact_keys(payloads, *names)
    assert values, f"missing false boolean for {names}\n{text}"
    assert any(value is False for value in values), values


def assert_any_true(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_exact_keys(payloads, *names)
    assert values, f"missing true boolean for {names}\n{text}"
    assert any(value is True for value in values), values


def assert_key_terms_false(payloads: list[Any], text: str, *terms: str) -> None:
    values = bool_values_for_key_terms(payloads, *terms)
    assert values, f"missing boolean key with terms {terms}\n{text}"
    assert all(value is False for value in values), values


def assert_any_key_terms_true(
    payloads: list[Any],
    text: str,
    *term_sets: tuple[str, ...],
) -> None:
    values: list[bool] = []
    for terms in term_sets:
        values.extend(bool_values_for_key_terms(payloads, *terms))
    assert values, f"missing boolean key with terms {term_sets}\n{text}"
    assert any(value is True for value in values), values


def assert_no_global_proof_or_promotion(payloads: list[Any], text: str) -> None:
    assert_any_false(payloads, text, "global_proof", "global_proof_closed")
    assert_any_false(
        payloads,
        text,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
        "promotion_allowed",
    )
    assert_any_true(payloads, text, "no_global_proof")
    assert_any_true(payloads, text, "no_promotion")
    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_nonlocal_source_zero_number_failure_emits_fail_closed_artifacts(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_nonlocal_zero_number_failure(tmp_path)
    combined = "\n".join([text, compact_text(payloads), compact_text(rows)])

    assert out_dir.name == STEM
    assert_text_has_all(
        combined,
        STEM,
        "nonlocal",
        "psi1",
        "source",
        "zero",
        "number",
        "commutator",
        "log",
        "hazard",
        "comparison",
        "envelope",
        ZERO_NUMBER_SYMBOL,
    )
    assert rows_mentioning(rows, "nonlocal", "psi1", "source"), combined
    assert rows_mentioning(rows, "commutator", "log", "hazard"), combined
    assert rows_mentioning(rows, "no", "comparison", "envelope"), combined
    assert rows_mentioning(rows, "missing", ZERO_NUMBER_SYMBOL), combined

    assert_any_false(payloads, text, "coupled_zero_number_proved")
    assert_any_false(
        payloads,
        text,
        "comparison_envelope_exists",
        "comparison_envelope_constructed",
    )
    assert_key_terms_false(payloads, text, "comparison", "envelope")
    assert_any_key_terms_true(
        payloads,
        text,
        ("artifact", "valid"),
        ("artifact", "complete"),
        ("artifact", "emitted"),
    )
    assert_any_key_terms_true(
        payloads,
        text,
        ("invariant", "valid"),
        ("invariant", "checked"),
        ("invariant", "preserved"),
    )
    assert_no_global_proof_or_promotion(payloads, text)


def test_sprint144_agda_receipt_is_imported_by_everything() -> None:
    assert EVERYTHING.is_file(), "missing " + str(EVERYTHING.relative_to(REPO_ROOT))
    source = EVERYTHING.read_text(encoding="utf-8")

    pattern = re.compile(rf"^\s*import\s+{re.escape(SPRINT144_MODULE)}\s*$", re.MULTILINE)
    assert pattern.search(source), (
        "DASHI/Everything.agda must import " + SPRINT144_MODULE
    )


def test_sprint144_agda_receipt_typechecks_if_present() -> None:
    if not SPRINT144_RECEIPT.is_file():
        pytest.skip("Sprint 144 Agda receipt is not present yet")

    result = subprocess.run(
        [
            "agda",
            "-i",
            ".",
            "-i",
            "DCHoTT-Agda",
            "-i",
            "cubical",
            "-l",
            "standard-library",
            str(SPRINT144_RECEIPT.relative_to(REPO_ROOT)),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
