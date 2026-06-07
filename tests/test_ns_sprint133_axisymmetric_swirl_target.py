from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint133_axisymmetric_swirl_target"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
SUMMARY_NAME = f"{STEM}_summary.json"
GATES_JSON_NAME = f"{STEM}_gates.json"
GATES_CSV_NAME = f"{STEM}_gates.csv"
REPORT_NAME = f"{STEM}.md"

EXPECTED_TARGET = "axisymmetric_ns_with_swirl_global_regularity"
EXPECTED_GATE_IDS = {
    "large_re_axisymmetric_transient_control",
    "marginal_beta_zero_analysis",
    "axisymmetric_symmetry_class_exhaustion",
    "axisymmetric_swirl_global_assembly",
}
EXPECTED_DEPENDENCY_TERMS = {
    "large_re_axisymmetric_transient_control": ("sprint130", "sprint131", "sprint132"),
    "marginal_beta_zero_analysis": ("sprint130", "sprint131"),
    "axisymmetric_symmetry_class_exhaustion": ("sprint132",),
    "axisymmetric_swirl_global_assembly": ("sprint130", "sprint131", "sprint132"),
}

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_target(tmp_path: Path) -> tuple[subprocess.CompletedProcess[str], Path, dict[str, Any], list[dict[str, Any]], list[dict[str, Any]], str]:
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

    text = artifact_text(out_dir, result) if out_dir.exists() else result.stdout + result.stderr
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text

    summary_path = out_dir / SUMMARY_NAME
    gates_json_path = out_dir / GATES_JSON_NAME
    gates_csv_path = out_dir / GATES_CSV_NAME
    report_path = out_dir / REPORT_NAME
    for path in (summary_path, gates_json_path, gates_csv_path, report_path):
        assert path.is_file(), f"missing output {path.name}\n{text}"
        assert path.stat().st_size > 0, f"empty output {path.name}"

    summary = load_json_object(summary_path)
    gates_json = load_rows_json(gates_json_path)
    gates_csv = load_rows_csv(gates_csv_path)
    return result, out_dir, summary, gates_json, gates_csv, text


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
        rows = payload.get("gates") or payload.get("rows") or payload.get("gap_list")
    else:
        rows = None
    assert isinstance(rows, list) and rows, f"{path.name} must contain nonempty gate rows"
    assert all(isinstance(row, dict) for row in rows), f"non-object gate row in {path.name}"
    return rows


def load_rows_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        rows = [dict(row) for row in csv.DictReader(handle)]
    assert rows, f"{path.name} must contain gate rows"
    return rows


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def bool_values_for_keys(payload: Any, *keys: str) -> list[bool]:
    wanted = set(keys)
    values: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if key in wanted and isinstance(value, bool):
                values.append(value)
    return values


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def gate_id(row: dict[str, Any]) -> str:
    value = row.get("gate_id") or row.get("id") or row.get("name") or row.get("gap_id")
    assert isinstance(value, str) and value, f"gate row missing id/name: {row}"
    return normalize_id(value)


def normalize_id(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "_", value.strip().lower()).strip("_")


def finite_flag(row: dict[str, Any]) -> bool:
    for key in ("finite", "finite_gate", "is_finite", "bounded", "gap_finite"):
        value = row.get(key)
        if isinstance(value, bool):
            return value
        if isinstance(value, str) and value.lower() in {"true", "false"}:
            return value.lower() == "true"
    text = json_text(row).lower()
    return "finite" in text and "infinite" not in text


def dependency_text(row: dict[str, Any]) -> str:
    values: list[str] = []
    for key in ("dependencies", "dependency_surfaces", "repo_support", "supporting_surfaces", "inputs"):
        value = row.get(key)
        if value is not None:
            values.append(json_text(value).lower())
    values.append(json_text(row).lower())
    return "\n".join(values)


def clay_guard_flags(summary: dict[str, Any]) -> list[tuple[str, bool]]:
    rows: list[tuple[str, bool]] = []
    for item in walk(summary):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if isinstance(value, bool) and "clay" in str(key).lower():
                rows.append((str(key), value))
    return rows


def test_sprint133_axisymmetric_swirl_target_cli_writes_json_csv_report(tmp_path: Path) -> None:
    _result, out_dir, summary, gates_json, gates_csv, text = run_target(tmp_path)

    assert out_dir.name == STEM
    assert summary.get("contract", STEM) == STEM
    assert gates_json, text
    assert gates_csv, text
    assert "axisymmetric" in text.lower()
    assert "swirl" in text.lower()


def test_sprint133_target_is_defined_and_stays_below_full_clay(tmp_path: Path) -> None:
    _result, _out_dir, summary, _gates_json, _gates_csv, text = run_target(tmp_path)

    assert summary.get("target_defined") is True, json_text(summary)
    assert normalize_id(str(summary.get("target", summary.get("target_id", "")))) == EXPECTED_TARGET

    full_clay_flags = bool_values_for_keys(summary, "full_clay_ns_solved", "full_clay_solved")
    clay_promotion_flags = bool_values_for_keys(
        summary,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    assert full_clay_flags and all(value is False for value in full_clay_flags), json_text(summary)
    assert clay_promotion_flags and all(value is False for value in clay_promotion_flags), json_text(summary)

    for key, value in clay_guard_flags(summary):
        if key in {"clay_absent", "clay_not_promoted", "no_clay_promotion_detected"}:
            continue
        assert value is False, f"Clay guard flag unexpectedly true: {(key, value)}"
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_sprint133_records_exactly_four_finite_axisymmetric_gates(tmp_path: Path) -> None:
    _result, _out_dir, summary, gates_json, gates_csv, text = run_target(tmp_path)

    json_gate_ids = {gate_id(row) for row in gates_json}
    csv_gate_ids = {gate_id(row) for row in gates_csv}
    assert json_gate_ids == EXPECTED_GATE_IDS, text
    assert csv_gate_ids == EXPECTED_GATE_IDS, text

    assert summary.get("finite_gate_count") == 4, json_text(summary)
    assert len(gates_json) == 4
    assert len(gates_csv) == 4
    assert all(finite_flag(row) for row in gates_json), json_text(gates_json)
    assert all(finite_flag(row) for row in gates_csv), json_text(gates_csv)


def test_sprint133_finite_gap_list_is_named_and_no_enumeration_exhaustion_claim(tmp_path: Path) -> None:
    _result, _out_dir, summary, gates_json, _gates_csv, _text = run_target(tmp_path)

    gap_list = summary.get("finite_gap_list") or summary.get("axisymmetric_gap_list") or summary.get("gates")
    assert isinstance(gap_list, list) and len(gap_list) == 4, json_text(summary)
    assert {normalize_id(str(item)) for item in gap_list} == EXPECTED_GATE_IDS

    assert summary.get("finite_gap_list_defined") is True
    assert summary.get("mechanism_enumeration_claim") is False
    assert summary.get("axisymmetric_class_only") is True
    assert all("axisymmetric" in json_text(row).lower() for row in gates_json)


def test_sprint133_gate_dependencies_reference_prior_sprint_surfaces(tmp_path: Path) -> None:
    _result, _out_dir, _summary, gates_json, gates_csv, text = run_target(tmp_path)

    by_gate = {gate_id(row): row for row in gates_json}
    csv_by_gate = {gate_id(row): row for row in gates_csv}
    for gate, required_terms in EXPECTED_DEPENDENCY_TERMS.items():
        combined = dependency_text(by_gate[gate]) + "\n" + dependency_text(csv_by_gate[gate])
        for term in required_terms:
            assert term in combined, f"{gate} missing dependency term {term!r}\n{text}"

