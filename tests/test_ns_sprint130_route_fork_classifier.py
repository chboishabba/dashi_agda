from __future__ import annotations

import json
import re
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_DIR = REPO_ROOT / "scripts"

CLASSIFIER = SCRIPT_DIR / "ns_sprint130_route_fork_classifier.py"
CONTRACT = "ns_sprint130_route_fork_classifier"
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_NAME = CONTRACT + "_rows.json"
REPORT_NAME = CONTRACT + ".md"

REQUIRED_ROWS = (
    "MarginalScalingCaseAnalysis",
    "EulerBlowupIsolation",
    "RegularityConclusion",
)
REQUIRED_EULER_GAPS = (
    "NoLogAxisymmetricBiotSavartUniform",
    "SourceAlignmentWithVorticityMaximum",
)
RECOMMENDED_FORK = "RegularityConclusion"


def json_values(payload: Any) -> Iterable[Any]:
    if isinstance(payload, dict):
        yield payload
        for value in payload.values():
            yield from json_values(value)
    elif isinstance(payload, list):
        for value in payload:
            yield from json_values(value)
    else:
        yield payload


def dicts_with_terms(payload: Any, *terms: str) -> list[dict[str, Any]]:
    matches: list[dict[str, Any]] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payload):
        if not isinstance(item, dict):
            continue
        item_text = json.dumps(item, sort_keys=True).lower()
        if all(term in item_text for term in folded_terms):
            matches.append(item)
    return matches


def bool_values_for_keys_containing(payload: Any, *terms: str) -> list[bool]:
    values: list[bool] = []
    folded_terms = tuple(term.lower() for term in terms)
    for item in json_values(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if not isinstance(value, bool):
                continue
            key_text = str(key).lower()
            if all(term in key_text for term in folded_terms):
                values.append(value)
    return values


def payload_text(*payloads: Any) -> str:
    return json.dumps(payloads, sort_keys=True)


def artifact_text(*paths: Path) -> str:
    return "\n".join(path.read_text(encoding="utf-8", errors="replace") for path in paths)


def recommended_fork(summary: dict[str, Any]) -> Any:
    return summary.get(
        "recommended_fork",
        summary.get("recommended_next_fork", summary.get("recommended_next_gate")),
    )


def run_classifier(
    tmp_path: Path,
) -> tuple[subprocess.CompletedProcess[str], dict[str, Any], Any, str]:
    assert CLASSIFIER.exists(), "Worker 6 classifier is missing: " + str(CLASSIFIER)

    out_dir = tmp_path / CONTRACT
    result = subprocess.run(
        [sys.executable, str(CLASSIFIER), "--out-dir", str(out_dir)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )

    summary_path = out_dir / SUMMARY_NAME
    rows_path = out_dir / ROWS_NAME
    report_path = out_dir / REPORT_NAME

    output_text = "\n".join(
        (
            result.stdout,
            result.stderr,
            artifact_text(
                *[path for path in (summary_path, rows_path, report_path) if path.is_file()]
            ),
        )
    )

    assert summary_path.is_file(), output_text
    assert rows_path.is_file(), output_text
    assert report_path.is_file(), output_text

    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    rows = json.loads(rows_path.read_text(encoding="utf-8"))
    return result, summary, rows, output_text


def test_sprint130_route_fork_classifier_script_exists() -> None:
    assert CLASSIFIER.is_file(), "missing " + str(CLASSIFIER.relative_to(REPO_ROOT))


def test_sprint130_cli_writes_summary_rows_report_and_exits_1(tmp_path: Path) -> None:
    result, summary, rows, output_text = run_classifier(tmp_path)
    text = payload_text(summary, rows)

    assert result.returncode == 1, output_text
    assert re.search(
        r'"recommended_(?:next_)?fork"\s*:\s*"' + re.escape(RECOMMENDED_FORK) + r'"',
        text,
    ), output_text
    assert RECOMMENDED_FORK in output_text


def test_sprint130_rows_contain_required_route_forks_and_euler_gaps(
    tmp_path: Path,
) -> None:
    _result, _summary, rows, output_text = run_classifier(tmp_path)

    for row_name in REQUIRED_ROWS:
        assert dicts_with_terms(rows, row_name), output_text

    for gap_name in REQUIRED_EULER_GAPS:
        assert dicts_with_terms(rows, "euler", gap_name), output_text


def test_sprint130_recommends_regularity_and_records_route_flags(
    tmp_path: Path,
) -> None:
    _result, summary, rows, output_text = run_classifier(tmp_path)

    assert recommended_fork(summary) == RECOMMENDED_FORK
    assert summary.get("hou_luo_ns_route_obstructed") is True, output_text
    assert summary.get("euler_route_open_not_ns") is True, output_text
    assert dicts_with_terms(rows, "hou", "luo", "obstructed"), output_text
    assert dicts_with_terms(rows, "euler", "open", "not", "ns"), output_text


def test_sprint130_classifier_has_no_clay_promotion_true(tmp_path: Path) -> None:
    _result, summary, rows, output_text = run_classifier(tmp_path)
    payloads = [summary, rows]

    clay_values = bool_values_for_keys_containing(payloads, "clay")
    assert clay_values and not any(clay_values), output_text
    assert not re.search(r"clay[A-Za-z0-9_]*\s*[:=]\s*true", output_text)
