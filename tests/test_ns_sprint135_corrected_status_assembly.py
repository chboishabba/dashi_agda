from __future__ import annotations

import csv
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint135_corrected_status_assembly"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"

EXPECTED_RETRACTED_CLAIMS = {
    "PureDiffusionU1MaximumPrinciple",
    "AxisymmetricHouLuoNSViscousDominanceObstruction",
}
EXPECTED_FALSE_LEMMAS = {"NoLogAxisymmetricBiotSavartUniform"}
EXPECTED_WBF_EXACT = {"WBF-L", "WBF-S", "WBF-MP", "WBF-R"}

CLAY_TRUE_PATTERNS = (
    re.compile(r'"clay[^"]*"\s*:\s*true\b', re.IGNORECASE),
    re.compile(r"\bclay[A-Za-z0-9_]*\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bfull[_\s-]*clay[_\s-]*ns[_\s-]*solved\b\s*[:=]\s*true\b", re.IGNORECASE),
    re.compile(r"\bclay[_\s-]*navier[_\s-]*stokes[_\s-]*promot\w*\b\s*[:=]\s*true\b", re.IGNORECASE),
)


def run_corrected_status(
    tmp_path: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, str]], str]:
    assert SCRIPT.is_file(), f"missing Worker 3 script: {SCRIPT.relative_to(REPO_ROOT)}"

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

    text = collect_artifact_text(out_dir, result)
    assert result.returncode == 0, text
    assert out_dir.is_dir(), text

    json_paths = sorted(out_dir.glob("*.json"))
    csv_paths = sorted(out_dir.glob("*.csv"))
    md_paths = sorted(out_dir.glob("*.md"))
    assert json_paths, text
    assert csv_paths, text
    assert md_paths, text
    assert all(path.stat().st_size > 0 for path in json_paths + csv_paths + md_paths)

    json_payloads = [json.loads(path.read_text(encoding="utf-8")) for path in json_paths]
    summary = merge_json_objects(json_payloads)
    rows_json = flatten_rows(json_payloads)
    rows_csv = load_csv_rows(csv_paths)
    assert summary, "expected at least one JSON object summary"
    assert rows_json or rows_csv, "expected JSON or CSV status rows"
    return summary, rows_json, rows_csv, text


def collect_artifact_text(out_dir: Path, result: subprocess.CompletedProcess[str]) -> str:
    paths: list[Path] = []
    if out_dir.exists():
        paths = sorted(
            path
            for path in out_dir.glob("*")
            if path.suffix.lower() in {".json", ".csv", ".md", ".txt"}
        )
    return "\n".join(
        [result.stdout, result.stderr]
        + [path.read_text(encoding="utf-8", errors="replace") for path in paths]
    )


def merge_json_objects(payloads: list[Any]) -> dict[str, Any]:
    merged: dict[str, Any] = {}
    for payload in payloads:
        if isinstance(payload, dict):
            merged.update(payload)
    return merged


def flatten_rows(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        rows: list[dict[str, Any]] = []
        for key in (
            "rows",
            "status_rows",
            "result_rows",
            "claims",
            "claim_rows",
            "lemma_rows",
            "boundary_rows",
            "theorem_rows",
            "retractions",
            "false_lemmas",
        ):
            child = value.get(key)
            if isinstance(child, list):
                rows.extend(row for row in child if isinstance(row, dict))
        if looks_like_row(value):
            rows.append(value)
        for child in value.values():
            rows.extend(flatten_rows(child))
        return rows
    if isinstance(value, list):
        return [row for child in value for row in flatten_rows(child)]
    return []


def looks_like_row(value: dict[str, Any]) -> bool:
    if set(value) == {"key", "value"}:
        return False
    row_keys = {
        "row_id",
        "result",
        "mechanism",
        "route",
        "status",
        "classification",
        "claim",
        "lemma",
        "theorem",
        "boundary",
    }
    return bool(row_keys.intersection(value))


def load_csv_rows(paths: Iterable[Path]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for path in paths:
        with path.open(newline="", encoding="utf-8") as handle:
            rows.extend(dict(row) for row in csv.DictReader(handle))
    return rows


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def artifact_json_text(*values: Any) -> str:
    return "\n".join(
        json.dumps(value, sort_keys=True, default=str)
        if not isinstance(value, str)
        else value
        for value in values
    )


def norm(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "-", str(value).lower()).strip("-")


def row_text(row: dict[str, Any]) -> str:
    return norm(artifact_json_text(row))


def row_mentions(row: dict[str, Any], *needles: str) -> bool:
    text = row_text(row)
    return all(norm(needle) in text for needle in needles)


def bool_values_for_key_fragments(payload: Any, *fragments: str) -> list[tuple[str, bool]]:
    found: list[tuple[str, bool]] = []
    wanted = tuple(fragment.lower() for fragment in fragments)
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if isinstance(value, bool) and any(fragment in str(key).lower() for fragment in wanted):
                found.append((str(key), value))
    return found


def list_values_for_key_fragments(payload: Any, *fragments: str) -> list[Any]:
    found: list[Any] = []
    wanted = tuple(fragment.lower() for fragment in fragments)
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if any(fragment in str(key).lower() for fragment in wanted):
                if isinstance(value, list):
                    found.extend(value)
                else:
                    found.append(value)
    return found


def test_sprint135_corrected_status_writes_json_csv_and_markdown(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)

    assert summary.get("contract", STEM) == STEM
    assert rows_json or rows_csv
    assert "corrected" in text.lower()
    assert "hou" in text.lower()
    assert "luo" in text.lower()


def test_sprint135_live_boundary_is_hou_luo_axisymmetric_with_swirl_open_candidate(
    tmp_path: Path,
) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)
    all_rows = rows_json + rows_csv
    joined = norm(artifact_json_text(summary, all_rows, text))

    assert "hou-luo" in joined
    assert "axisymmetric" in joined
    assert "swirl" in joined
    assert "open" in joined
    assert "candidate" in joined

    boundary_values = list_values_for_key_fragments(
        summary,
        "live_boundary",
        "live_route",
        "route_status",
        "boundary_status",
    )
    assert boundary_values or any(
        row_mentions(row, "Hou", "Luo", "axisymmetric", "swirl")
        and row_mentions(row, "open", "candidate")
        for row in all_rows
    )
    assert "obstructed" not in joined or "not-obstructed" in joined or "false" in joined


def test_sprint135_retracted_claims_include_bad_u1_diffusion_and_axis_obstruction(
    tmp_path: Path,
) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)
    all_rows = rows_json + rows_csv
    joined = artifact_json_text(summary, all_rows, text)

    for claim in EXPECTED_RETRACTED_CLAIMS:
        assert claim in joined, f"missing retracted claim {claim}\n{joined}"
        matching_rows = [
            row
            for row in all_rows
            if claim.lower() in artifact_json_text(row).lower()
            and ("retract" in row_text(row) or "supersed" in row_text(row))
        ]
        assert matching_rows or "retracted" in joined.lower(), claim

    retraction_values = list_values_for_key_fragments(summary, "retracted")
    retraction_text = artifact_json_text(retraction_values, all_rows).lower()
    assert "purediffusionu1maximumprinciple".lower() in retraction_text
    assert "axisymmetrichouluonsviscousdominanceobstruction".lower() in retraction_text


def test_sprint135_false_lemmas_include_uniform_no_log_biot_savart(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)
    all_rows = rows_json + rows_csv
    joined = artifact_json_text(summary, all_rows, text)

    for lemma in EXPECTED_FALSE_LEMMAS:
        assert lemma in joined, f"missing false lemma {lemma}\n{joined}"
        lemma_rows = [
            row
            for row in all_rows
            if lemma.lower() in artifact_json_text(row).lower()
            and ("false" in row_text(row) or "invalid" in row_text(row))
        ]
        assert lemma_rows or "false_uniform" in joined.lower() or "false lemmas" in joined.lower()


def test_sprint135_wbf_exact_obstructions_remain_intact(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)
    all_rows = rows_json + rows_csv
    joined = artifact_json_text(summary, all_rows, text)

    assert "wbf" in joined.lower()
    assert bool_values_for_key_fragments(summary, "wbf")
    for key, value in bool_values_for_key_fragments(summary, "wbf"):
        if "intact" in key.lower() or "exact" in key.lower():
            assert value is True, (key, value)

    for label in EXPECTED_WBF_EXACT:
        matching = [
            row
            for row in all_rows
            if label.lower() in artifact_json_text(row).lower()
            and "exact" in row_text(row)
            and "intact" in row_text(row)
        ]
        assert matching or label in joined, f"missing intact exact WBF row for {label}\n{text}"


def test_sprint135_keeps_clay_flags_false(tmp_path: Path) -> None:
    summary, rows_json, rows_csv, text = run_corrected_status(tmp_path)
    payload = [summary, rows_json, rows_csv]

    clay_flags = bool_values_for_key_fragments(payload, "clay")
    assert clay_flags, "expected explicit Clay guard flags"
    for key, value in clay_flags:
        if key.lower() in {"clay_absent", "clay_not_promoted", "no_clay_promotion_detected"}:
            continue
        assert value is False, f"Clay flag must remain false: {(key, value)}"

    full_clay_flags = [
        value
        for key, value in clay_flags
        if "full" in key.lower() and "clay" in key.lower()
    ]
    assert full_clay_flags and all(value is False for value in full_clay_flags)

    for pattern in CLAY_TRUE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
