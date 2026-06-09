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

COMMUTATOR_STEM = "ns_sprint141_commutator_domination_inequality"
LOG_SAMPLER_STEM = "ns_sprint141_biot_savart_log_commutator_sampler"

CLAY_TRUE_PATTERNS = (
    re.compile(r'"full_clay_ns_solved"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r'"clay_navier_stokes_promoted"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bpromotion[_\s-]*decision\b\s*[:=]\s*(?:promote|promoted)\b", re.IGNORECASE),
)

TRUE_PROOF_PATTERNS = (
    re.compile(r'"(?:proved|proven|global_proof|unconditional_proof)"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\b(?:proved|proven|global[_\s-]*proof|unconditional[_\s-]*proof)\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_sprint141_script(
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
    text = str(value)
    replacements = {
        "∂": "partial",
        "ᵣ": "r",
        "ᶻ": "z",
        "θ": "theta",
        "^": " ",
        "-": "_",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    return re.sub(r"[^a-z0-9]+", "_", text.lower()).strip("_")


def compact_text(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def rows_from_artifacts(payloads: list[Any], csv_paths: list[Path]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    row_key_terms = {
        "row_id",
        "hazard_id",
        "hazard_name",
        "claim_id",
        "inequality_id",
        "sample_id",
        "gate",
    }
    for item in walk(payloads):
        if isinstance(item, dict) and any(normalize(key) in row_key_terms for key in item):
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


def assert_terms(text: str, *terms: str) -> None:
    haystack = normalize(text)
    missing = [term for term in terms if normalize(term) not in haystack]
    assert not missing, f"missing terms {missing}\n{text}"


def assert_false_flags(payloads: list[Any], text: str, *names: str) -> None:
    values = bool_values_for_keys(payloads, *names)
    assert values, f"missing explicit false flags for {names}\n{text}"
    assert all(value is False for value in values), values


def assert_fail_closed_summary_flags(payloads: list[Any], text: str) -> None:
    combined = compact_text([payloads, text])
    assert "fail_closed" in combined, text
    assert_false_flags(
        payloads,
        text,
        "global_proof_closed",
        "global_proof",
        "domination_closed",
        "commutator_domination_closed",
        "claim_closed",
    )


def assert_named_rows_and_hazards(rows: list[dict[str, Any]], text: str) -> None:
    named_rows = [
        row
        for row in rows
        if any(
            normalize(key)
            in {"row_id", "hazard_id", "hazard_name", "claim_id", "inequality_id", "sample_id"}
            for key in row
        )
    ]
    assert named_rows, f"missing named rows\n{text}"

    hazard_rows = [row for row in named_rows if "hazard" in compact_text(row)]
    assert hazard_rows, f"missing named hazard rows\n{text}"
    for row in hazard_rows:
        assert any(str(value).strip() for value in row.values()), row


def assert_absent_constants_and_log_aware_theorem(text: str) -> None:
    compact = normalize(text)
    assert "constant" in compact or "constants" in compact, text
    assert any(term in compact for term in {"absent", "missing", "unavailable", "not_available"}), text
    assert "log_aware" in compact, text
    assert "theorem" in compact, text
    assert any(
        term in compact
        for term in {
            "log_aware_theorem_absent",
            "log_aware_domination_theorem_absent",
            "log_aware_commutator_theorem_absent",
            "missing_log_aware_theorem",
        }
    ), text


def assert_no_clay_solution_or_promotion(payloads: list[Any], text: str) -> None:
    assert_false_flags(payloads, text, "full_clay_ns_solved", "full_clay_solved")
    assert_false_flags(
        payloads,
        text,
        "clay_navier_stokes_promoted",
        "clayNavierStokesPromoted",
        "clay_promoted",
    )
    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
    for pattern in TRUE_PROOF_PATTERNS:
        assert not pattern.search(text), pattern.pattern


def test_commutator_domination_inequality_is_fail_closed_without_constants(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint141_script(tmp_path, COMMUTATOR_STEM)
    combined = "\n".join([text, compact_text(payloads), compact_text(rows)])

    assert out_dir.name == COMMUTATOR_STEM
    assert_terms(
        combined,
        COMMUTATOR_STEM,
        "commutator",
        "domination",
        "inequality",
        "constant",
        "log aware",
    )
    assert_named_rows_and_hazards(rows, text)
    assert_absent_constants_and_log_aware_theorem(combined)
    assert_fail_closed_summary_flags(payloads, text)
    assert_no_clay_solution_or_promotion(payloads, text)


def test_biot_savart_log_commutator_sampler_records_log_hazards_without_promotion(
    tmp_path: Path,
) -> None:
    payloads, rows, text, out_dir = run_sprint141_script(tmp_path, LOG_SAMPLER_STEM)
    combined = "\n".join([text, compact_text(payloads), compact_text(rows)])

    assert out_dir.name == LOG_SAMPLER_STEM
    assert_terms(
        combined,
        LOG_SAMPLER_STEM,
        "biot",
        "savart",
        "log",
        "commutator",
        "sampler",
        "hazard",
    )
    assert_named_rows_and_hazards(rows, text)
    assert_absent_constants_and_log_aware_theorem(combined)
    assert_fail_closed_summary_flags(payloads, text)
    assert_no_clay_solution_or_promotion(payloads, text)
