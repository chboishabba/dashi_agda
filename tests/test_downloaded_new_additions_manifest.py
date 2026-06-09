import json
import re
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "downloaded_new_additions_manifest.py"
SOURCE_DIR = REPO_ROOT / "temp-DOWNLOADED" / "new additions"


HEX64 = re.compile(r"^[0-9a-f]{64}$")
EXPECTED_ROW_COUNT = 36
EXPECTED_VERSION = "1.0.0"


def _run_manifest(tmp_path: Path) -> tuple[dict, str]:
    if not SOURCE_DIR.exists():
        pytest.skip(f"downloaded additions directory is absent: {SOURCE_DIR}")
    if not SCRIPT.exists():
        pytest.skip(f"manifest CLI is absent: {SCRIPT}")

    output_dir = tmp_path / "manifest"
    result = subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--source-dir",
            str(SOURCE_DIR),
            "--output-dir",
            str(output_dir),
            "--generated-at",
            "2026-06-07T00:00:00+00:00",
        ],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout

    json_outputs = sorted(output_dir.glob("*.json"))
    markdown_outputs = sorted(output_dir.glob("*.md"))
    assert json_outputs, "CLI should emit at least one JSON manifest"
    assert markdown_outputs, "CLI should emit at least one Markdown report"

    manifest = json.loads(json_outputs[0].read_text(encoding="utf-8"))
    markdown = markdown_outputs[0].read_text(encoding="utf-8")
    assert markdown.strip()
    return manifest, markdown


def _rows(manifest: dict) -> list[dict]:
    rows = manifest.get("rows")
    assert isinstance(rows, list), "manifest JSON should expose a top-level rows list"
    return rows


def _row_field(row: dict, *names: str):
    for name in names:
        if name in row:
            return row[name]
    return None


def test_downloaded_new_additions_manifest_cli_emits_checked_surface(tmp_path: Path):
    manifest, _markdown = _run_manifest(tmp_path)
    rows = _rows(manifest)

    assert manifest.get("schema") == "dashi-downloaded-new-additions-reference-index-v1"
    assert manifest.get("schema_version") == EXPECTED_VERSION
    assert len(rows) == EXPECTED_ROW_COUNT

    for row in rows:
        sha256 = _row_field(row, "sha256", "sourceSha256", "source_sha256")
        assert isinstance(sha256, str), row
        assert HEX64.fullmatch(sha256), row

    promotion = manifest.get("promotion_flags", manifest.get("promotion", manifest.get("promotionFlags", {})))
    assert isinstance(promotion, dict)
    assert promotion, "manifest should expose explicit promotion flags"
    assert all(value is False for value in promotion.values())


def test_downloaded_new_additions_manifest_covers_file_families_and_tags(tmp_path: Path):
    manifest, markdown = _run_manifest(tmp_path)
    rows = _rows(manifest)

    filenames = {
        _row_field(row, "filename", "name", "path", "relativePath", "relative_path")
        for row in rows
    }
    filenames = {str(name) for name in filenames if name is not None}
    suffixes = {Path(name).suffix.lower() for name in filenames}

    assert ".pdf" in suffixes
    assert suffixes & {".png", ".webp"}
    assert suffixes & {".csv", ".json"}
    assert suffixes & {".py", ".agda", ".html"}

    tag_blob = json.dumps(rows, sort_keys=True).lower() + "\n" + markdown.lower()
    assert "hodge" in tag_blob
    assert "ym" in tag_blob or "yang" in tag_blob
    assert "string" in tag_blob
