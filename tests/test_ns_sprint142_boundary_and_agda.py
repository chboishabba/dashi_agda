from __future__ import annotations

import csv
import json
import re
import shutil
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint142_boundary_annulus_concavity_ledger"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT142_MODULE = (
    "DASHI.Physics.Closure.NSSprint142GlobalConcavityObstructionReceipt"
)
SPRINT142_RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint142GlobalConcavityObstructionReceipt.agda"
)

TRUE_COMPLETION_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_proof_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_barrier_closed"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
    re.compile(r"\bglobal[_\s-]*proof[_\s-]*(?:closed|proved|proven)\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_boundary_ledger(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
    assert SCRIPT.is_file(), "missing " + str(SCRIPT.relative_to(REPO_ROOT))

    out_dir = REPO_ROOT / "outputs" / ".pytest" / tmp_path.name / STEM
    if out_dir.exists():
        shutil.rmtree(out_dir)
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

    assert result.returncode == 0, artifact_text
    assert out_dir.is_dir(), artifact_text
    assert json_paths, artifact_text
    assert csv_paths, artifact_text
    assert md_paths, artifact_text
    assert all(path.stat().st_size > 0 for path in [*json_paths, *csv_paths, *md_paths])

    payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    rows = rows_from_artifacts(payloads, csv_paths)
    assert rows, artifact_text
    shutil.rmtree(out_dir.parent, ignore_errors=True)
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
    text = str(value)
    replacements = {
        "Gamma": "gamma",
        "kappa": "kappa",
        "^": " ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return re.sub(r"[^a-z0-9]+", "_", text.lower()).strip("_")


def compact_text(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_keys = {
        "claim_id",
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


def test_boundary_annulus_concavity_ledger_emits_fail_closed_artifacts(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_boundary_ledger(tmp_path)
    combined = "\n".join([text, compact_text(payloads), compact_text(rows)])

    assert out_dir.name == STEM
    assert_text_has_all(
        combined,
        STEM,
        "boundary",
        "annulus",
        "concavity",
        "global",
        "blocker",
        "fail",
        "closed",
    )
    assert rows_mentioning(rows, "boundary", "image"), combined
    assert rows_mentioning(rows, "annular", "hazard"), combined
    assert rows_mentioning(rows, "boundary", "compatible", "theorem"), combined
    assert rows_mentioning(rows, "global", "concavity", "blocker"), combined

    assert_any_false(payloads, text, "annular_shoulder_theorem_exists")
    assert_any_false(
        payloads,
        text,
        "boundary_compatible_kernel_sign_or_cancellation_theorem_exists",
        "required_theorem_available",
    )
    assert_key_terms_false(payloads, text, "boundary", "compatible", "theorem")
    assert_any_false(payloads, text, "global_concavity_closed")
    assert_no_global_proof_or_promotion(payloads, text)


def test_sprint142_agda_receipt_is_imported_by_everything() -> None:
    assert EVERYTHING.is_file(), "missing " + str(EVERYTHING.relative_to(REPO_ROOT))
    source = EVERYTHING.read_text(encoding="utf-8")

    pattern = re.compile(rf"^\s*import\s+{re.escape(SPRINT142_MODULE)}\s*$", re.MULTILINE)
    assert pattern.search(source), (
        "DASHI/Everything.agda must import " + SPRINT142_MODULE
    )


def test_sprint142_agda_receipt_typechecks_if_present() -> None:
    if not SPRINT142_RECEIPT.is_file():
        pytest.skip("Sprint 142 Agda receipt is not present yet")

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
            str(SPRINT142_RECEIPT.relative_to(REPO_ROOT)),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    assert result.returncode == 0, result.stdout + result.stderr
