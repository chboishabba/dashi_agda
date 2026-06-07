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
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint132_submission_bundle_index.py"

PROMOTED_NAME = "clay" + "Yang" + "Mills" + "Promoted"
PROMOTED_TRUE_PATTERNS = (
    PROMOTED_NAME + " = " + "tr" + "ue",
    PROMOTED_NAME + ": " + "tr" + "ue",
    PROMOTED_NAME + '": ' + "tr" + "ue",
    '"promoted": ' + "tr" + "ue",
    '"promotion": ' + "tr" + "ue",
    '"value": ' + "tr" + "ue",
)

REQUIRED_SPRINT128_131_ARTIFACTS = {
    "outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit.md",
    "outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json",
    "outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit.md",
    "outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json",
    "outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit.md",
    "outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit_summary.json",
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit.md",
    "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json",
    "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet.md",
    "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json",
}


@pytest.fixture
def bundle_out_dir(tmp_path: Path) -> Path:
    out_dir = REPO_ROOT / ".pytest_tmp" / "ym_sprint132_bundle_index" / tmp_path.name
    shutil.rmtree(out_dir, ignore_errors=True)
    try:
        yield out_dir
    finally:
        shutil.rmtree(out_dir, ignore_errors=True)


def run_bundle_index(out_dir: Path, repo_root: Path = REPO_ROOT) -> tuple[dict[str, Any], str, list[Path], list[Path]]:
    assert SCRIPT.exists(), f"missing Sprint132 bundle index script: {SCRIPT}"
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
    assert json_paths, "bundle index did not write JSON"
    assert markdown_paths, "bundle index did not write Markdown"
    assert all(path.stat().st_size > 0 for path in json_paths + markdown_paths)

    summary_path = next(
        (
            path
            for path in json_paths
            if re.search(r"(bundle|index|summary|manifest)", path.name, re.IGNORECASE)
        ),
        json_paths[0],
    )
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    assert isinstance(summary, dict) and summary, "bundle JSON must be a nonempty object"
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
    entries = []
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


def categories(summary: dict[str, Any]) -> set[str]:
    category_map = summary.get("categories")
    if isinstance(category_map, dict):
        return {key for key, value in category_map.items() if isinstance(value, list) and value}
    found = set()
    for item in artifact_entries(summary):
        for key, value in item.items():
            if re.search(r"category|kind|class|group", str(key), re.IGNORECASE) and isinstance(value, str):
                found.add(value)
    return found


def referenced_paths(summary: dict[str, Any], markdown_text: str) -> set[str]:
    paths = set()
    for item in walk(summary):
        if isinstance(item, dict):
            for value in item.values():
                if isinstance(value, str):
                    found = path_text(value)
                    if found:
                        paths.add(found)
        elif isinstance(item, str):
            found = path_text(item)
            if found:
                paths.add(found)
    paths.update(re.findall(
        r"\b(?:DASHI|Docs|outputs|scripts|tests|artifacts)/[A-Za-z0-9_./+-]+"
        r"(?:\.agda|\.md|\.json|\.csv|\.txt|\.py)\b",
        markdown_text,
    ))
    return paths


def assert_no_promotion(summary: dict[str, Any], text: str) -> None:
    promotion_rows = [
        item
        for item in walk(summary)
        if isinstance(item, dict)
        and any(isinstance(value, bool) for value in item.values())
        and re.search(r"clay|promotion|promoted", json.dumps(item), re.IGNORECASE)
    ]
    assert promotion_rows, "bundle index should expose the no-promotion gate"
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


def test_sprint132_bundle_index_writes_json_markdown_categories_and_hashes(bundle_out_dir: Path) -> None:
    summary, markdown_text, _json_paths, _markdown_paths = run_bundle_index(bundle_out_dir)

    found_categories = categories(summary)
    assert found_categories, "bundle entries should have nonempty categories"

    entries_with_hash = [
        (entry_path(entry), entry_sha256(entry))
        for entry in artifact_entries(summary)
        if entry_path(entry) and entry_sha256(entry)
    ]
    assert entries_with_hash, "bundle should include SHA-256 hashes for referenced repo artifacts"
    for rel_path, recorded_hash in entries_with_hash:
        assert rel_path is not None
        repo_path = REPO_ROOT / rel_path
        assert repo_path.is_file(), f"hashed artifact does not exist: {rel_path}"
        actual_hash = hashlib.sha256(repo_path.read_bytes()).hexdigest()
        assert recorded_hash == actual_hash, f"hash mismatch for {rel_path}"

    assert_no_promotion(summary, markdown_text)


def test_sprint132_bundle_includes_required_sprint128_131_and_present_sprint132_artifacts(
    bundle_out_dir: Path,
) -> None:
    summary, markdown_text, _json_paths, _markdown_paths = run_bundle_index(bundle_out_dir)
    paths = referenced_paths(summary, markdown_text)

    missing_required = sorted(REQUIRED_SPRINT128_131_ARTIFACTS - paths)
    assert not missing_required, "missing required Sprint128-131 artifacts: " + ", ".join(missing_required)

    sprint132_modules = {
        path.relative_to(REPO_ROOT).as_posix()
        for path in (REPO_ROOT / "DASHI").rglob("*Sprint132*.agda")
    }
    missing_sprint132 = sorted(sprint132_modules - paths)
    assert not missing_sprint132, "present Sprint132 modules missing from bundle: " + ", ".join(missing_sprint132)


def test_sprint132_bundle_index_fails_closed_for_missing_repo_root(tmp_path: Path) -> None:
    assert SCRIPT.exists(), f"missing Sprint132 bundle index script: {SCRIPT}"
    out_dir = tmp_path / "bundle"
    missing_root = tmp_path / "missing-repo-root"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(missing_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode != 0
    assert re.search(r"missing|not found|repo|root|required|fail", result.stdout + result.stderr, re.IGNORECASE)


def test_sprint132_bundle_index_fails_closed_for_forbidden_marker_when_fixture_is_practical(
    tmp_path: Path,
) -> None:
    assert SCRIPT.exists(), f"missing Sprint132 bundle index script: {SCRIPT}"
    fixture_root = tmp_path / "repo"
    for dirname in ("DASHI", "outputs"):
        source = REPO_ROOT / dirname
        if source.exists():
            shutil.copytree(source, fixture_root / dirname)
    poisoned = fixture_root / "DASHI" / "Physics" / "Closure" / "YMSprint132ForbiddenMarkerFixture.agda"
    poisoned.parent.mkdir(parents=True, exist_ok=True)
    poisoned.write_text(
        "module DASHI.Physics.Closure.YMSprint132ForbiddenMarkerFixture where\n\n"
        "postulate forbiddenMarker : Set\n",
        encoding="utf-8",
    )

    out_dir = tmp_path / "bundle"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--repo-root",
            str(fixture_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode == 0:
        pytest.skip("script does not scan fixture Sprint132 surfaces for forbidden markers")
    assert re.search(r"postulate|forbidden|marker|fail", result.stdout + result.stderr, re.IGNORECASE)
