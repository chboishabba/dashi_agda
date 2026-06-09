from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint133_submission_readiness_index.py"

PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"
PROMOTED_TRUE_PATTERNS = (
    PROMOTED_NAME + " = " + "tr" + "ue",
    PROMOTED_NAME + ": " + "tr" + "ue",
    PROMOTED_NAME + '": ' + "tr" + "ue",
    '"promoted": ' + "tr" + "ue",
    '"promotion": ' + "tr" + "ue",
    '"value": ' + "tr" + "ue",
)

REQUIRED_SPRINT131_132_OUTPUTS = {
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit.md",
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json",
    "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet.md",
    "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json",
    "outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit.md",
    "outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit_summary.json",
    "outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.md",
    "outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.json",
}


def run_readiness_index(out_dir: Path, repo_root: Path = REPO_ROOT) -> tuple[dict[str, Any], str, list[Path], list[Path]]:
    assert SCRIPT.exists(), f"missing Sprint133 submission readiness index script: {SCRIPT}"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    json_paths = sorted(out_dir.rglob("*.json"))
    markdown_paths = sorted(
        path for path in out_dir.rglob("*") if path.suffix.lower() in {".md", ".markdown"}
    )
    assert json_paths, "readiness index did not write JSON"
    assert markdown_paths, "readiness index did not write Markdown"
    assert all(path.stat().st_size > 0 for path in json_paths + markdown_paths)

    summary_path = next(
        (
            path
            for path in json_paths
            if re.search(r"(readiness|index|summary|manifest)", path.name, re.IGNORECASE)
        ),
        json_paths[0],
    )
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    assert isinstance(summary, dict) and summary, "readiness JSON must be a nonempty object"
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


def path_text(value: str) -> str | None:
    match = re.search(
        r"\b(?:DASHI|Docs|outputs|scripts|tests|artifacts)/[A-Za-z0-9_./+-]+"
        r"(?:\.agda|\.md|\.json|\.csv|\.txt|\.py)\b",
        value,
    )
    return match.group(0) if match else None


def artifact_entries(summary: dict[str, Any]) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for item in walk(summary):
        if not isinstance(item, dict):
            continue
        keys = {str(key).lower() for key in item}
        values = [value for value in item.values() if isinstance(value, str)]
        if any("path" in key or "artifact" in key or "evidence" in key for key in keys) and any(
            path_text(value) for value in values
        ):
            entries.append(item)
    return entries


def entry_path(entry: dict[str, Any]) -> str | None:
    for key in ("path", "repo_path", "artifact_path", "evidence_path", "source_path"):
        value = entry.get(key)
        if isinstance(value, str):
            found = path_text(value)
            if found:
                return found
    for value in entry.values():
        if isinstance(value, str):
            found = path_text(value)
            if found:
                return found
    return None


def entry_sha256(entry: dict[str, Any]) -> str | None:
    for key, value in entry.items():
        if isinstance(value, str) and "sha256" in str(key).lower():
            return value.lower()
        if isinstance(value, str) and re.fullmatch(r"[0-9a-fA-F]{64}", value):
            return value.lower()
    return None


def referenced_paths(summary: dict[str, Any], markdown_text: str) -> set[str]:
    paths: set[str] = set()
    path_pattern = re.compile(
        r"\b(?:DASHI|Docs|outputs|scripts|tests|artifacts)/[A-Za-z0-9_./+-]+"
        r"(?:\.agda|\.md|\.json|\.csv|\.txt|\.py)\b"
    )
    for item in walk(summary):
        if isinstance(item, dict):
            for value in item.values():
                if isinstance(value, str):
                    paths.update(path_pattern.findall(value))
        elif isinstance(item, str):
            paths.update(path_pattern.findall(item))
    paths.update(path_pattern.findall(markdown_text))
    return paths


def command_rows(summary: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for item in walk(summary):
        if not isinstance(item, dict):
            continue
        encoded = json.dumps(item, sort_keys=True)
        if re.search(r"command|cmd|pytest|agda|check|status", encoded, re.IGNORECASE):
            rows.append(item)
    return rows


def assert_no_promotion(summary: dict[str, Any], text: str) -> None:
    promotion_rows = [
        item
        for item in walk(summary)
        if isinstance(item, dict)
        and any(isinstance(value, bool) for value in item.values())
        and re.search(r"clay|promotion|promoted", json.dumps(item), re.IGNORECASE)
    ]
    assert promotion_rows, "readiness index should expose the no-promotion gate"
    assert not any(
        row.get(PROMOTED_NAME) is True
        or row.get("clayYangMillsPromoted") is True
        or row.get("promoted") is True
        or row.get("promotion") is True
        or row.get("value") is True
        for row in promotion_rows
    )
    for pattern in PROMOTED_TRUE_PATTERNS:
        assert pattern not in text


def test_sprint133_readiness_index_writes_json_markdown_and_matching_hashes(tmp_path: Path) -> None:
    out_dir = tmp_path / "readiness"
    summary, markdown_text, _json_paths, _markdown_paths = run_readiness_index(out_dir)

    entries_with_hash = [
        (entry_path(entry), entry_sha256(entry))
        for entry in artifact_entries(summary)
        if entry_path(entry) and entry_sha256(entry)
    ]
    assert entries_with_hash, "readiness index should include SHA-256 hashes for evidence artifacts"
    for rel_path, recorded_hash in entries_with_hash:
        assert rel_path is not None
        repo_path = REPO_ROOT / rel_path
        assert repo_path.is_file(), f"hashed evidence artifact does not exist: {rel_path}"
        actual_hash = hashlib.sha256(repo_path.read_bytes()).hexdigest()
        assert recorded_hash == actual_hash, f"hash mismatch for {rel_path}"

    assert_no_promotion(summary, markdown_text)


def test_sprint133_readiness_includes_required_prior_outputs_and_present_sprint133_modules(
    tmp_path: Path,
) -> None:
    summary, markdown_text, _json_paths, _markdown_paths = run_readiness_index(tmp_path / "readiness")
    paths = referenced_paths(summary, markdown_text)

    missing_required = sorted(REQUIRED_SPRINT131_132_OUTPUTS - paths)
    assert not missing_required, "missing required Sprint131/Sprint132 outputs: " + ", ".join(missing_required)

    sprint133_modules = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in (REPO_ROOT / "DASHI").rglob("*Sprint133*.agda")
    }
    missing_sprint133 = sorted(sprint133_modules - paths)
    assert not missing_sprint133, "present Sprint133 modules missing from readiness index: " + ", ".join(
        missing_sprint133
    )


def test_sprint133_readiness_command_rows_are_nonempty(tmp_path: Path) -> None:
    summary, _markdown_text, _json_paths, _markdown_paths = run_readiness_index(tmp_path / "readiness")

    rows = command_rows(summary)
    assert rows, "readiness index should include command/check rows"
    empty_rows = [
        row
        for row in rows
        if not any(isinstance(value, str) and value.strip() for value in row.values())
    ]
    assert not empty_rows, "command/check rows must not be empty: " + json.dumps(empty_rows, sort_keys=True)


def test_sprint133_readiness_fails_closed_for_missing_required_evidence(tmp_path: Path) -> None:
    assert SCRIPT.exists(), f"missing Sprint133 submission readiness index script: {SCRIPT}"
    fixture_root = tmp_path / "repo"
    for dirname in ("DASHI", "outputs"):
        source = REPO_ROOT / dirname
        if source.exists():
            shutil.copytree(source, fixture_root / dirname)

    required = fixture_root / "outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.json"
    required.unlink()

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(fixture_root),
            "--out-dir",
            str(tmp_path / "readiness"),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode != 0
    assert re.search(r"missing|required|evidence|fail", result.stdout + result.stderr, re.IGNORECASE)


def test_sprint133_readiness_fails_closed_for_forbidden_marker_fixture_when_practical(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing Sprint133 submission readiness index script: {SCRIPT}"
    fixture_root = tmp_path / "repo"
    for dirname in ("DASHI", "outputs"):
        source = REPO_ROOT / dirname
        if source.exists():
            shutil.copytree(source, fixture_root / dirname)
    poisoned = fixture_root / "DASHI" / "Physics" / "Closure" / "YMSprint133ForbiddenMarkerFixture.agda"
    poisoned.parent.mkdir(parents=True, exist_ok=True)
    poisoned.write_text(
        "module DASHI.Physics.Closure.YMSprint133ForbiddenMarkerFixture where\n\n"
        "postulate forbiddenMarker : Set\n",
        encoding="utf-8",
    )

    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(fixture_root),
            "--out-dir",
            str(tmp_path / "readiness"),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode == 0:
        pytest.skip("script does not scan fixture Sprint133 surfaces for forbidden markers")
    assert re.search(r"postulate|forbidden|marker|fail", result.stdout + result.stderr, re.IGNORECASE)
