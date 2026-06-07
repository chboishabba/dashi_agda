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
STEM = "ns_sprint145_source_commutator_alignment_sampler"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT145_MODULE = (
    "DASHI.Physics.Closure.NSSprint145ComparisonEnvelopeObstructionReceipt"
)
SPRINT145_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint145ComparisonEnvelopeObstructionReceipt.agda"
)

MISSING_ENVELOPE = "ComparisonEnvelopeForNonlocalPsi1AndRadialCommutators"

TRUE_COMPLETION_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"comparison_envelope(?:_proved|_available|_exists)?"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_alignment_theorem(?:_proved)?"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
    re.compile(r"\bglobal[_\s-]*proof[_\s-]*(?:closed|proved|proven)\b\s*[:=]\s*true\b", re.IGNORECASE),
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
        "scenario_id",
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


def assert_key_terms_false(payloads: list[Any], text: str, *terms: str) -> None:
    values = bool_values_for_key_terms(payloads, *terms)
    assert values, f"missing boolean key with terms {terms}\n{text}"
    assert all(value is False for value in values), values


def assert_any_true(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_exact_keys(payloads, *names)
    assert values, f"missing true boolean for {names}\n{text}"
    assert any(value is True for value in values), values


def assert_no_global_alignment_envelope_proof_or_promotion(
    payloads: list[Any],
    text: str,
) -> None:
    assert_any_false(
        payloads,
        text,
        "global_alignment_theorem",
        "global_alignment_theorem_proved",
    )
    assert_any_false(
        payloads,
        text,
        "comparison_envelope_available",
        "comparison_envelope_proved",
        "comparison_envelope_exists",
    )
    assert_any_false(payloads, text, "global_proof", "global_proof_closed")
    assert_any_false(
        payloads,
        text,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "promotion_allowed",
    )
    assert_any_true(payloads, text, "no_global_proof")
    assert_any_true(payloads, text, "no_promotion")
    for pattern in TRUE_COMPLETION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def run_alignment_sampler(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    if not SCRIPT.is_file():
        pytest.skip("Sprint 145 source/commutator alignment sampler is not present yet")

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


def test_alignment_sampler_records_adverse_reinforcement_fail_closed(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_alignment_sampler(tmp_path)
    combined = "\n".join([text, compact_text(payloads), compact_text(rows)])

    assert out_dir.name == STEM
    assert_text_has_all(
        combined,
        STEM,
        "source",
        "commutator",
        "alignment",
        "adverse",
        "reinforcement",
        MISSING_ENVELOPE,
    )
    assert rows_mentioning(rows, "source", "commutator", "alignment"), combined
    assert rows_mentioning(rows, "adverse", "reinforcement"), combined
    assert rows_mentioning(rows, "comparison", "envelope"), combined
    assert rows_mentioning(rows, "global", "alignment"), combined

    assert_any_false(
        payloads,
        text,
        "global_alignment_theorem",
        "global_alignment_theorem_proved",
        "source_commutator_alignment_theorem_proved",
    )
    assert_any_false(
        payloads,
        text,
        "comparison_envelope_available",
        "comparison_envelope_proved",
        "comparison_envelope_exists",
        "comparison_envelope_constructed",
    )
    assert_no_global_alignment_envelope_proof_or_promotion(payloads, text)


def test_sprint145_agda_receipt_content_if_present() -> None:
    if not SPRINT145_RECEIPT.is_file():
        pytest.skip("Sprint 145 Agda receipt is not present yet")

    source = SPRINT145_RECEIPT.read_text(encoding="utf-8")
    assert_text_has_all(
        source,
        "module",
        SPRINT145_MODULE,
        MISSING_ENVELOPE,
        "clayNavierStokesPromoted",
        "false",
    )
    assert "full_clay_ns_solved" in source or "fullClayNSSolved" in source
    assert "globalAlignmentTheorem" in source or "global_alignment_theorem" in source
    assert "comparisonEnvelope" in source or "ComparisonEnvelope" in source


def test_sprint145_agda_receipt_is_imported_by_everything_if_present() -> None:
    if not SPRINT145_RECEIPT.is_file():
        pytest.skip("Sprint 145 Agda receipt is not present yet")

    assert EVERYTHING.is_file(), "missing " + str(EVERYTHING.relative_to(REPO_ROOT))
    source = EVERYTHING.read_text(encoding="utf-8")

    pattern = re.compile(rf"^\s*import\s+{re.escape(SPRINT145_MODULE)}\s*$", re.MULTILINE)
    assert pattern.search(source), (
        "DASHI/Everything.agda must import " + SPRINT145_MODULE
    )


def test_sprint145_agda_receipt_typechecks_if_present() -> None:
    if not SPRINT145_RECEIPT.is_file():
        pytest.skip("Sprint 145 Agda receipt is not present yet")

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
            str(SPRINT145_RECEIPT.relative_to(REPO_ROOT)),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
