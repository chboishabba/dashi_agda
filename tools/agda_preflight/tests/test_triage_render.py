from pathlib import Path

from agda_preflight.checker import Diagnostic
from agda_preflight.triage_render import (
    build_triage,
    render_compact,
    render_grouped,
    render_location,
    render_verbose,
)


def d(code, message, path, line, column=1, *, severity="error", evidence="dashi-index", minimum=None):
    return Diagnostic(
        code,
        message,
        Path(path),
        line,
        column,
        severity=severity,
        evidence=evidence,
        minimum_evidence=minimum or evidence,
    )


def sample(root: Path):
    path = root / "DASHI" / "Moonshine" / "Bundle.agda"
    return [
        d("TSAGDA049", "projection Render.klein is under-applied", path, 380, 21),
        d(
            "TSAGDA052",
            "Render.klein is used without a visible JPhaseRenderingAlgebra receiver",
            path,
            380,
            21,
        ),
        d("TSAGDA204", "Exact module contains unresolved proof placeholder", path, 392, 19, evidence="tree-sitter"),
        d("TSAGDA204", "Exact module contains unresolved proof placeholder", path, 396, 51, evidence="tree-sitter"),
        d("TSAGDA053", "Tower.reflectPoint is visibly over-applied (2>1)", path, 420, 8),
        d(
            "TSAGDA120",
            "field JointFiniteDihedralReceipt.phase6 has known term jointFiniteTInverse in type-head position",
            path,
            619,
        ),
        d(
            "TSAGDA123",
            "projection JointFiniteDihedralReceipt.phase6 has known term jointFiniteTInverse in type position",
            path,
            619,
        ),
    ]


def test_grouped_render_uses_relative_paths_and_merges_compatible_siblings(tmp_path):
    triage = build_triage(sample(tmp_path), tmp_path)
    output = render_grouped(triage)

    assert "DASHI/Moonshine/Bundle.agda" in output
    assert str(tmp_path) not in output
    assert "TSAGDA049/052" in output
    assert output.count("380:21") == 1
    assert "TSAGDA120/123" in output
    assert "Root causes" in output
    assert "fingerprint: preflight:" in output


def test_compact_render_is_one_logical_issue_per_line(tmp_path):
    triage = build_triage(sample(tmp_path), tmp_path)
    output = render_compact(triage)

    lines = [line for line in output.splitlines() if "380:21" in line]
    assert len(lines) == 1
    assert "049/052" in lines[0]
    assert "receiver" in lines[0]
    assert "Render.klein" in lines[0]


def test_location_render_orders_by_source_location(tmp_path):
    triage = build_triage(list(reversed(sample(tmp_path))), tmp_path)
    output = render_location(triage)

    positions = [output.index(location) for location in ("380:21", "392:19", "396:51", "420:8", "619:1")]
    assert positions == sorted(positions)


def test_verbose_render_preserves_each_raw_diagnostic_and_absolute_path_option(tmp_path):
    diagnostics = sample(tmp_path)
    triage = build_triage(diagnostics, tmp_path, absolute_paths=True)
    output = render_verbose(triage)

    assert str(tmp_path) in output
    for code in ("TSAGDA049", "TSAGDA052", "TSAGDA120", "TSAGDA123"):
        assert code in output
    assert "[evidence=dashi-index; requires=dashi-index]" in output


def test_only_kind_filters_logical_clusters(tmp_path):
    triage = build_triage(sample(tmp_path), tmp_path, only_kind="placeholder")
    output = render_grouped(triage)

    assert "TSAGDA204" in output
    assert "TSAGDA049" not in output
    assert "TSAGDA053" not in output


def test_fingerprint_is_stable_under_input_order(tmp_path):
    first = build_triage(sample(tmp_path), tmp_path)
    second = build_triage(list(reversed(sample(tmp_path))), tmp_path)

    assert first.fingerprint == second.fingerprint


def test_evidence_is_prominent_when_requirement_differs(tmp_path):
    path = tmp_path / "DASHI" / "Deferred.agda"
    diagnostics = [
        d(
            "TSAGDA022",
            "unknown alias use",
            path,
            10,
            evidence="dashi-index",
            minimum="agda-scope",
        )
    ]
    output = render_grouped(build_triage(diagnostics, tmp_path))

    assert "evidence: dashi-index → requires agda-scope" in output
