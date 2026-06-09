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

COUPLED_ZERO_NUMBER_STEM = "ns_sprint144_coupled_zero_number_interface"
RZ_TOPOLOGY_STEM = "ns_sprint144_rz_crossing_topology_sampler"

TRUE_SOLUTION_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)

TRUE_CLOSURE_PATTERNS = (
    re.compile(r'"coupled_zero_number_theorem_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"scalar_transfer_valid"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"fixed_line_zero_count_sufficient"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"secondary_peak_exclusion_proved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"global_barrier_closed"\s*:\s*true\b', re.IGNORECASE),
)

ROW_KEYS = {
    "artifact_id",
    "blocker_id",
    "case_id",
    "claim_id",
    "id",
    "invariant_id",
    "ledger_id",
    "name",
    "obstruction_id",
    "row_id",
    "scenario",
    "scenario_id",
    "status",
}


def run_sprint144_script(
    tmp_path: Path,
    stem: str,
) -> tuple[list[Any], list[dict[str, Any]], str, Path]:
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


def assert_true_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing explicit true flags for {names}\n{text}"
    assert all(value is True for value in values), values


def assert_named_rows(rows: list[dict[str, Any]], text: str) -> None:
    normalized_row_keys = {normalize(key) for key in ROW_KEYS}
    named_rows = [
        row
        for row in rows
        if any(normalize(key) in normalized_row_keys for key in row)
        and any(str(value).strip() for value in row.values())
    ]
    assert named_rows, f"missing named rows/scenarios\n{text}"


def assert_support_rows(
    rows: list[dict[str, Any]],
    text: str,
    *term_sets: tuple[str, ...],
) -> None:
    assert any(rows_with_terms(rows, *terms) for terms in term_sets), (
        f"missing support row/scenario for {term_sets}\n" + text
    )


def assert_adverse_obstruction_rows(rows: list[dict[str, Any]], text: str, *terms: str) -> None:
    rows_found = (
        rows_with_terms(rows, *terms, "obstruction")
        or rows_with_terms(rows, *terms, "adverse")
        or rows_with_terms(rows, *terms, "blocker")
    )
    assert rows_found, (
        f"missing {'/'.join(terms)} adverse obstruction row/scenario\n" + text
    )
    adverse_text = compact(rows)
    assert any(
        term in adverse_text for term in {"adverse", "blocker", "missing", "obstruction"}
    ), "missing adverse/blocker/missing/obstruction classification\n" + text


def assert_missing_theorem_and_constants(text: str, *, require_constants: bool) -> None:
    compact_text = normalize(text)
    assert "theorem" in compact_text, text
    if require_constants:
        assert "constant" in compact_text or "constants" in compact_text, text
    assert any(term in compact_text for term in {"absent", "missing", "unavailable", "not_available"}), text
    assert not any(pattern.search(text) for pattern in TRUE_CLOSURE_PATTERNS), text


def assert_no_solution_or_promotion(payloads: list[Any], text: str) -> None:
    assert_false_flags(payloads, text, "full_clay_ns_solved")
    assert_false_flags(payloads, text, "clay_navier_stokes_promoted")
    for pattern in TRUE_SOLUTION_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def assert_sprint144_contract(
    stem: str,
    payloads: list[Any],
    rows: list[dict[str, Any]],
    text: str,
    out_dir: Path,
    require_constants: bool,
) -> None:
    combined = "\n".join([text, compact(payloads), compact(rows)])

    assert out_dir.name == stem
    assert_terms(combined, stem)
    assert_named_rows(rows, text)
    assert_missing_theorem_and_constants(combined, require_constants=require_constants)

    assert_false_flags(payloads, text, "coupled_zero_number_theorem_proved")
    assert_false_flags(payloads, text, "secondary_peak_exclusion_proved")
    assert_false_flags(payloads, text, "global_barrier_closed")
    assert_no_solution_or_promotion(payloads, text)
    assert_true_flags(payloads, text, "artifact_complete")
    assert_true_flags(payloads, text, "invariants_passed")


def test_coupled_zero_number_interface_records_obstructions_without_promotion(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint144_script(tmp_path, COUPLED_ZERO_NUMBER_STEM)
    assert_sprint144_contract(
        COUPLED_ZERO_NUMBER_STEM,
        payloads,
        rows,
        text,
        out_dir,
        require_constants=True,
    )
    assert_support_rows(rows, text, ("scalar", "support"), ("scalar", "template"))
    assert_adverse_obstruction_rows(rows, text, "coupled")
    assert_false_flags(payloads, text, "scalar_transfer_valid")


def test_rz_crossing_topology_sampler_records_obstructions_without_promotion(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint144_script(tmp_path, RZ_TOPOLOGY_STEM)
    assert_sprint144_contract(
        RZ_TOPOLOGY_STEM,
        payloads,
        rows,
        text,
        out_dir,
        require_constants=False,
    )
    assert_support_rows(rows, text, ("scalar", "support"), ("fixed", "line", "support"))
    if not rows_with_terms(rows, "rz", "obstruction"):
        assert_adverse_obstruction_rows(rows, text, "r", "z")
    else:
        assert_adverse_obstruction_rows(rows, text, "rz")
    assert_false_flags(payloads, text, "fixed_line_zero_count_sufficient")
