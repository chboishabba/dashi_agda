from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint131_submission_packet_builder.py"
DEFAULT_OUT_DIR = REPO_ROOT / "outputs" / "ym_sprint131_submission_packet"

PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"
PROMOTED_TRUE_PATTERNS = (
    PROMOTED_NAME + " = " + "tr" + "ue",
    PROMOTED_NAME + ": " + "tr" + "ue",
    PROMOTED_NAME + '": ' + "tr" + "ue",
    '"promoted": ' + "tr" + "ue",
    '"promotion": ' + "tr" + "ue",
)


def run_builder(out_dir: Path) -> tuple[dict[str, Any], str, list[Path], list[Path]]:
    assert SCRIPT.exists(), f"missing Sprint 131 submission packet builder: {SCRIPT}"
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
    assert result.returncode == 0, result.stdout + result.stderr

    emitted_paths = [
        REPO_ROOT / line.strip()
        for line in result.stdout.splitlines()
        if line.strip() and (REPO_ROOT / line.strip()).exists()
    ]
    output_dirs = [out_dir, DEFAULT_OUT_DIR]
    output_dirs.extend(path.parent for path in emitted_paths)
    output_dirs = list(dict.fromkeys(output_dirs))

    json_paths = sorted(
        {
            path
            for directory in output_dirs
            for path in directory.glob("*.json")
            if "sprint131" in path.name
        }
    )
    markdown_paths = sorted(
        {
            path
            for directory in output_dirs
            for path in directory.glob("*")
            if "sprint131" in path.name and path.suffix.lower() in {".md", ".markdown"}
        }
    )
    assert json_paths, "builder did not write a JSON packet"
    assert markdown_paths, "builder did not write a Markdown packet"

    summary_path = next(
        (
            path
            for path in json_paths
            if re.search(r"(summary|packet)", path.name, re.IGNORECASE)
        ),
        json_paths[0],
    )
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    text = "\n".join(
        [json.dumps(summary, sort_keys=True)]
        + [path.read_text(encoding="utf-8") for path in markdown_paths]
    )
    return summary, text, json_paths, markdown_paths


def walk(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [item for child in value.values() for item in walk(child)]
    if isinstance(value, list):
        return [value] + [item for child in value for item in walk(child)]
    return [value]


def json_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True)


def bool_rows(summary: dict[str, Any], terms: tuple[str, ...]) -> list[dict[str, Any]]:
    pattern = re.compile("|".join(re.escape(term) for term in terms), re.IGNORECASE)
    return [
        item
        for item in walk(summary)
        if isinstance(item, dict)
        and any(isinstance(value, bool) for value in item.values())
        and pattern.search(json_text(item))
    ]


def packet_sections(markdown: str) -> list[str]:
    matches = list(re.finditer(r"(?m)^#{1,4}\s+\S.*$", markdown))
    assert matches, "Markdown packet should contain headings"
    sections: list[str] = []
    for index, match in enumerate(matches):
        if match.group(0).startswith("# ") and index + 1 < len(matches):
            continue
        end = matches[index + 1].start() if index + 1 < len(matches) else len(markdown)
        section = markdown[match.end() : end].strip()
        assert section, f"empty section after heading {match.group(0)!r}"
        sections.append(section)
    return sections


def referenced_repo_paths(summary: dict[str, Any], markdown_text: str) -> set[Path]:
    path_like = re.compile(
        r"\b(?:DASHI|Docs|outputs|scripts|tests|artifacts)/[A-Za-z0-9_./+-]+"
        r"(?:\.agda|\.md|\.json|\.csv|\.txt|\.py)\b"
    )
    candidates = set(path_like.findall(markdown_text))
    for item in walk(summary):
        if isinstance(item, dict):
            for key, value in item.items():
                if isinstance(value, str) and re.search(r"path|source|artifact|evidence", key, re.IGNORECASE):
                    candidates.update(path_like.findall(value))
                    if re.search(r"\.(agda|md|json|csv|txt|py)$", value):
                        candidates.add(value)
        elif isinstance(item, str):
            candidates.update(path_like.findall(item))

    return {REPO_ROOT / candidate for candidate in candidates}


def assert_no_promotion(summary: dict[str, Any], text: str) -> None:
    promotion_rows = bool_rows(summary, ("clay", "promotion", "promoted"))
    assert promotion_rows, "packet should expose the no-promotion gate"
    assert all(
        row.get(PROMOTED_NAME) is not True
        and row.get("clayYangMillsPromoted") is not True
        and row.get("promoted") is not True
        and row.get("promotion") is not True
        and row.get("value") is not True
        for row in promotion_rows
    )
    for pattern in PROMOTED_TRUE_PATTERNS:
        assert pattern not in text


def test_sprint131_builder_writes_json_and_markdown_packets(tmp_path: Path) -> None:
    out_dir = tmp_path / "packet"
    summary, text, json_paths, markdown_paths = run_builder(out_dir)

    assert all(path.stat().st_size > 0 for path in json_paths)
    assert all(path.stat().st_size > 0 for path in markdown_paths)
    assert re.search(r"Sprint\s*131|sprint131", text, re.IGNORECASE)
    assert isinstance(summary, dict) and summary


def test_sprint131_sections_are_nonempty_and_evidence_backed(tmp_path: Path) -> None:
    out_dir = tmp_path / "packet"
    summary, _text, _json_paths, markdown_paths = run_builder(out_dir)
    markdown_text = "\n".join(path.read_text(encoding="utf-8") for path in markdown_paths)

    sections = packet_sections(markdown_text)
    assert len(sections) >= 4, "submission packet should have multiple substantive sections"
    evidence_sections = [
        section
        for section in sections
        if re.search(r"\b(evidence|source|artifact|receipt|path|summary)\b", section, re.IGNORECASE)
        and re.search(r"\.(agda|md|json|csv|txt|py)\b|DASHI/|Docs/|outputs/|scripts/", section)
    ]
    assert len(evidence_sections) >= 3, "sections should cite concrete evidence artifacts"
    referenced = referenced_repo_paths(summary, markdown_text)
    assert referenced, "packet should reference existing repo paths"
    assert any(path.is_file() for path in referenced)


def test_sprint131_referenced_paths_exist(tmp_path: Path) -> None:
    out_dir = tmp_path / "packet"
    summary, _text, _json_paths, markdown_paths = run_builder(out_dir)
    markdown_text = "\n".join(path.read_text(encoding="utf-8") for path in markdown_paths)

    referenced = referenced_repo_paths(summary, markdown_text)
    assert referenced, "no referenced paths found"
    missing = [
        str(path.relative_to(REPO_ROOT))
        for path in referenced
        if not path.exists()
    ]
    assert not missing


def test_sprint131_internal_readiness_true_and_external_acceptance_absent(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "packet"
    summary, text, _json_paths, _markdown_paths = run_builder(out_dir)

    readiness_rows = bool_rows(summary, ("internal", "readiness", "ready"))
    readiness_rows.extend(bool_rows(summary, ("validation", "required", "clean")))
    assert readiness_rows or summary.get("internal_gate_rows"), "packet should expose internal readiness"
    assert any(
        row.get("internal_readiness") is True
        or row.get("internalReadiness") is True
        or row.get("ready") is True
        or row.get("readiness") is True
        or row.get("value") is True
        or row.get("required_evidence_files_present") is True
        or row.get("audit_fail_closed_scans_clean") is True
        for row in readiness_rows
    ) or all(
        row.get("closed") is True for row in summary.get("internal_gate_rows", [])
    ), "internal readiness should be true"

    acceptance_rows = bool_rows(summary, ("external", "acceptance", "accepted"))
    assert not any(
        row.get("external_acceptance") is True
        or row.get("externalAcceptance") is True
        or row.get("accepted") is True
        or row.get("value") is True
        for row in acceptance_rows
    ), "external acceptance must be absent, not granted"
    assert not re.search(r"\bexternal acceptance\b.{0,80}\b(true|granted|accepted)\b", text, re.IGNORECASE | re.DOTALL)


def test_sprint131_packet_does_not_promote(tmp_path: Path) -> None:
    out_dir = tmp_path / "packet"
    summary, text, _json_paths, _markdown_paths = run_builder(out_dir)

    assert_no_promotion(summary, text)
    assert re.search(r"\b(no promotion|not promoted|not_promoted|fail-closed)\b", text, re.IGNORECASE)
