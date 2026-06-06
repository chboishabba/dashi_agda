from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint121_compact_group_parameter_table.py"
SUMMARY_NAME = "ym_sprint121_compact_group_parameter_table.json"
REPORT_NAME = "ym_sprint121_compact_group_parameter_table.md"
CLAY_NAME = "clay" + "Yang" + "Mills" + "Promoted"

pytestmark = pytest.mark.skipif(
    not SCRIPT.exists(),
    reason="Sprint121 compact group parameter table script is not integrated yet",
)

FORBIDDEN_TOKENS = (
    "post" + "ulate",
    "TO" + "DO",
    "stu" + "b",
    "{" + "!",
    "!" + "}",
    "PLACE" + "HOLDER",
    "XXX",
)
FORBIDDEN_PROMOTION = CLAY_NAME + " = " + "tr" + "ue"
FORBIDDEN_WORD_PATTERNS = {
    "post" + "ulate": re.compile(r"\bpost" + "ulate\b"),
    "TO" + "DO": re.compile(r"\bTO" + "DO\b"),
    "stu" + "b": re.compile(r"\bstu" + "b\b", re.IGNORECASE),
    "PLACE" + "HOLDER": re.compile(r"\bPLACE" + "HOLDER\b", re.IGNORECASE),
}


def run_script(out_dir: Path) -> dict[str, Any]:
    result = subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode in (0, 1), result.stdout + result.stderr

    summary_path = out_dir / SUMMARY_NAME
    if not summary_path.exists():
        candidates = sorted(out_dir.glob("*compact_group_parameter_table*.json"))
        assert candidates, result.stdout + result.stderr
        summary_path = candidates[0]
    return json.loads(summary_path.read_text(encoding="utf-8"))


def flatten_values(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for item in value.values() for nested in flatten_values(item)]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten_values(item)]
    return [value]


def normalized_words(value: Any) -> set[str]:
    return set(re.findall(r"[a-z0-9]+", json.dumps(value, sort_keys=True).lower()))


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def group_key(value: Any) -> str:
    return re.sub(r"[^a-z0-9]", "", str(value).lower())


def row_group_key(row: dict[str, Any]) -> str:
    for key in ("group", "group_name", "display_name", "key", "name", "compact_group", "lie_group"):
        if key in row:
            return group_key(row[key])
    return ""


def collect_group_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in flatten_values(summary):
        if not isinstance(item, dict):
            continue
        keys = {key.lower() for key in item}
        if keys & {"adjoint_dimension", "dim_adjoint", "adjoint_dim", "dimension_adjoint"}:
            rows.append(item)
        elif keys & {"adjoint_dimension_value", "adjoint_dimension_formula"}:
            rows.append(item)
    return rows


def find_group_row(summary: dict[str, Any], group_name: str) -> dict[str, Any]:
    target = group_key(group_name)
    aliases = {
        "su2": {"su2", "specialunitary2"},
        "su3": {"su3", "specialunitary3"},
        "g2": {"g2"},
        "e8": {"e8"},
    }.get(target, {target})
    for row in collect_group_rows(summary):
        key = row_group_key(row)
        if any(alias in key for alias in aliases):
            return row
    pytest.fail(f"missing compact group row for {group_name}")


def numeric_field(row: dict[str, Any], *names: str) -> int | float:
    aliases = {name.lower() for name in names}
    for key, value in row.items():
        normalized = key.lower()
        if normalized in aliases and isinstance(value, (int, float)):
            return value
        if normalized in aliases and isinstance(value, str) and re.fullmatch(r"-?\d+(\.\d+)?", value):
            return float(value) if "." in value else int(value)
    pytest.fail(f"missing numeric field {names} in {row}")


def k_g_value(row: dict[str, Any]) -> int | float:
    for key in (
        "k_G",
        "k_g",
        "kg",
        "k_G_conservative",
        "monotone_k_G",
        "monotone_k_g",
        "kappa_G",
        "kappa_g",
    ):
        if key in row:
            value = row[key]
            if isinstance(value, (int, float)):
                return value
            if isinstance(value, str) and re.fullmatch(r"-?\d+(\.\d+)?", value):
                return float(value) if "." in value else int(value)
    pytest.fail(f"missing monotone k_G field in {row}")


def output_text(out_dir: Path, summary: dict[str, Any]) -> str:
    parts = [json_text(summary)]
    for path in sorted(out_dir.glob("*")):
        if path.suffix in {".json", ".md", ".markdown", ".txt"}:
            parts.append(path.read_text(encoding="utf-8"))
    return "\n".join(parts)


def assert_no_forbidden_markers(text: str) -> None:
    for token in FORBIDDEN_TOKENS:
        if token in FORBIDDEN_WORD_PATTERNS:
            assert not FORBIDDEN_WORD_PATTERNS[token].search(text), token
        else:
            assert token not in text
    assert FORBIDDEN_PROMOTION not in text
    assert (CLAY_NAME + '": true') not in text
    assert (CLAY_NAME + " = true") not in text


def test_sprint121_exact_adjoint_dimensions_for_required_groups(tmp_path: Path) -> None:
    summary = run_script(tmp_path / "out")

    expected = {"SU(2)": 3, "SU(3)": 8, "G2": 14, "E8": 248}
    for group_name, dimension in expected.items():
        row = find_group_row(summary, group_name)
        assert numeric_field(
            row,
            "adjoint_dimension",
            "dim_adjoint",
            "adjoint_dim",
            "dimension_adjoint",
            "adjoint_dimension_value",
        ) == dimension


def test_sprint121_monotone_k_g_examples_are_ordered(tmp_path: Path) -> None:
    summary = run_script(tmp_path / "out")

    rows = [find_group_row(summary, group_name) for group_name in ("SU(2)", "SU(3)", "G2", "E8")]
    values = [k_g_value(row) for row in rows]

    assert values == sorted(values)
    assert len(set(values)) == len(values)
    assert values[0] > 0


def test_sprint121_cli_writes_json_and_markdown_outputs(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    report_path = out_dir / REPORT_NAME

    assert (out_dir / SUMMARY_NAME).exists() or sorted(out_dir.glob("*compact_group_parameter_table*.json"))
    assert report_path.exists() or sorted(out_dir.glob("*compact_group_parameter_table*.md"))
    report = (
        report_path
        if report_path.exists()
        else sorted(out_dir.glob("*compact_group_parameter_table*.md"))[0]
    ).read_text(encoding="utf-8")
    assert "Sprint 121" in report
    assert "SU(2)" in report
    assert "SU(3)" in report
    assert "G2" in report
    assert "E8" in report
    assert json_text(summary)


def test_sprint121_outputs_remain_non_promoting_and_marker_free(tmp_path: Path) -> None:
    out_dir = tmp_path / "out"
    summary = run_script(out_dir)
    text = output_text(out_dir, summary)

    assert_no_forbidden_markers(text)
    words = normalized_words(summary)
    assert "promotion" in words or "promoted" in words or "route" in words
    assert "true" not in {
        str(value).lower()
        for item in flatten_values(summary)
        if isinstance(item, dict)
        for key, value in item.items()
        if "promotion" in key.lower() or "promoted" in key.lower()
    }


def test_sprint121_script_source_has_no_forbidden_markers_or_promotion() -> None:
    source = SCRIPT.read_text(encoding="utf-8")

    assert_no_forbidden_markers(source)
