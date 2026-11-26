import json
import subprocess
import sys
from pathlib import Path

from scripts.round_similarity_bidi import analyze, normalize_round_name, render_review_markdown


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "round_similarity_bidi.py"
SOURCE = ROOT / ".dashi/round-stranded/ym-packages.jsonl"
CONFIG = ROOT / "config/round-similarity-tranches.json"


def test_round_normalization_and_empty_hash_exclusion():
    assert normalize_round_name("literalRound123FooRound9") == "<ROUND>Foo<ROUND>"
    report = analyze(SOURCE, CONFIG, [1])
    group = report["groups"][0]
    assert "" not in group["presence"]["body_hashes"]
    assert "" not in group["presence"]["signature_hashes"]


def test_verified_group_sizes_and_presence_intersections():
    report = analyze(SOURCE, CONFIG, [1, 2, 3])
    assert [group["package_count"] for group in report["groups"]] == [111, 98, 64]
    assert [group["declaration_count"] for group in report["groups"]] == [121, 99, 88]
    assert all(group["presence"]["normalized_declaration_names"] for group in report["groups"])
    pairs = {(row["group_a"], row["group_b"]): row for row in report["pairwise"]}
    assert len(pairs[(1, 2)]["shared_signatures"]) == 1
    assert all(not row["shared_normalized_symbols"] for row in pairs.values())


def test_group_three_retains_unresolved_and_superseded_evidence():
    group = analyze(SOURCE, CONFIG, [3])["groups"][0]
    assert group["status_counts"]["archive_status"] == {"SUPERSEDED": 1, "UNRESOLVED": 63}
    assert group["status_counts"]["unresolved_residual_entries"] > 0


def test_residual_audit_distinguishes_markers_from_missing_source():
    report = analyze(SOURCE, CONFIG, [3])
    from scripts.round_similarity_bidi import _audit_residuals

    audit = _audit_residuals(report["groups"], ROOT, "master", ["master", "origin/pr/1444"])
    critical = [item for item in audit["residuals"] if item["family"].endswith("YangMillsClayCriticalPath")]
    assert len(critical) == 30
    assert all(item["source_present"] and item["master_present"] for item in critical)
    assert all(item["validation_refl"] for item in critical)
    assert audit["missing_source_count"] == 0
    assert all(item["ref_presence"]["origin/pr/1444"] for item in critical)


def test_repeated_runs_are_byte_identical(tmp_path):
    first = tmp_path / "first.json"
    second = tmp_path / "second.json"
    for output in (first, second):
        subprocess.run(
            [sys.executable, str(SCRIPT), "--output", str(output)],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    assert first.read_bytes() == second.read_bytes()
    assert json.loads(first.read_text())["pairwise"]


def test_review_digest_contains_shared_occurrences_and_residual_queue():
    digest = render_review_markdown(analyze(SOURCE, CONFIG, [1, 2, 3]))
    assert "## Groups 1 and 2" in digest
    assert "### Shared signature occurrences" in digest
    assert "## Group 3 unresolved review queue" in digest


def test_cli_report_records_master_presence_audit(tmp_path):
    output = tmp_path / "report.json"
    review = tmp_path / "review.md"
    subprocess.run(
        [sys.executable, str(SCRIPT), "--groups", "3", "--output", str(output), "--review-output", str(review)],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    audit = json.loads(output.read_text())["residual_audit"]
    assert audit["residual_count"] == 63
    assert audit["existing_validation_marker_count"] == 63
    assert audit["missing_source_count"] == 0
    assert "Residual-marker audit" in review.read_text()
