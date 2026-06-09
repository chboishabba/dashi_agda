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
STEM = "ns_sprint140_failure_mode_matrix"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
SPRINT140_MODULE = (
    "DASHI.Physics.Closure.NSSprint140ConditionalBarrierAssemblyReceipt"
)

EXPECTED_FAILURE_MODES = {
    "conditional_barrier_assumption_unproved",
    "axisymmetric_barrier_route_open",
    "localized_kernel_sign_open",
    "pointwise_commutator_domination_open",
    "barrier_assembly_receipt_conditional_only",
    "global_regular_boundary_missing",
    "clay_problem_promotion_blocked",
}

TRUE_FLAG_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global[_ -]*proof[_ -]*(?:closed|proved|proven)"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"[^"]*(?:completed|proved|proven)[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(
        r"\b(?:full[_\s-]*clay[_\s-]*ns[_\s-]*solved|"
        r"clay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*|"
        r"global[_\s-]*proof\w*|completed|proved|proven)\b\s*[:=]\s*true\b",
        re.IGNORECASE,
    ),
)


def run_failure_matrix(tmp_path: Path) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
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
    for item in walk(payloads):
        if isinstance(item, dict) and any(
            normalize(key)
            in {
                "failure_mode",
                "failure_mode_id",
                "mode_id",
                "route_decision",
                "global_proof",
            }
            for key in item
        ):
            rows.append(item)
    for path in csv_paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def bool_values_for_keys(payload: Any, *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted and isinstance(value, bool):
                values.append(value)
    return values


def falseish(value: Any) -> bool:
    return value is False or normalize(value) in {"false", "0", "no", "not_proved", "open"}


def route_decisions(rows: list[dict[str, Any]], payloads: list[Any]) -> set[str]:
    decisions: set[str] = set()
    for item in walk([payloads, rows]):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) == "route_decision":
                decisions.add(normalize(value))
    return decisions


def failure_modes(rows: list[dict[str, Any]]) -> set[str]:
    modes: set[str] = set()
    for row in rows:
        for key, value in row.items():
            if normalize(key) in {"failure_mode", "failure_mode_id", "mode_id"}:
                mode = normalize(value)
                if mode:
                    modes.add(mode)
    return modes


def assert_false_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing explicit false flag for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_no_accidental_true_completion_or_proof(
    payloads: list[Any],
    rows: list[dict[str, Any]],
    text: str,
) -> None:
    for pattern in TRUE_FLAG_PATTERNS:
        assert not pattern.search(text), pattern.pattern

    for item in walk([payloads, rows]):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            normalized_key = normalize(key)
            if any(term in normalized_key for term in ("completed", "proved", "proven")):
                assert falseish(value), {key: value}


def test_sprint140_failure_mode_matrix_emits_fail_closed_open_artifacts(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_failure_matrix(tmp_path)
    combined = compact_text([payloads, rows, text])

    assert out_dir.name == STEM
    assert STEM in combined
    assert "conditional_barrier" in combined
    assert "failure_mode" in combined

    missing_modes = EXPECTED_FAILURE_MODES - failure_modes(rows)
    assert not missing_modes, f"missing failure modes {sorted(missing_modes)}\n{text}"

    decisions = route_decisions(rows, payloads)
    assert "fail_closed" in decisions, decisions
    assert "fail_open" in decisions, decisions

    assert_false_flags(payloads, text, "full_clay_ns_solved", "full_clay_solved")
    assert_false_flags(
        payloads,
        text,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    assert_false_flags(payloads, text, "global_proof", "global_proof_closed")
    assert_no_accidental_true_completion_or_proof(payloads, rows, text)


def test_sprint140_agda_receipt_is_imported_by_everything() -> None:
    assert EVERYTHING.is_file(), "missing " + str(EVERYTHING.relative_to(REPO_ROOT))
    source = EVERYTHING.read_text(encoding="utf-8")

    pattern = re.compile(rf"^\s*import\s+{re.escape(SPRINT140_MODULE)}\s*$", re.MULTILINE)
    assert pattern.search(source), (
        "DASHI/Everything.agda must import " + SPRINT140_MODULE
    )
