from pathlib import Path
from types import SimpleNamespace

from agda_preflight.boundary_refinements import _is_module_assignment_tsagda090
from agda_preflight.checker import Diagnostic


def test_module_assignment_is_not_treated_as_qualified_record_field(tmp_path):
    assignment = SimpleNamespace(
        name="Nested.Module",
        line=12,
        node=SimpleNamespace(type="module_assignment"),
    )
    summary = SimpleNamespace(
        ast=SimpleNamespace(
            record_expressions=[SimpleNamespace(assignments=[assignment])]
        )
    )
    diagnostic = Diagnostic(
        "TSAGDA090",
        "qualified record field Nested.Module is invalid in record construction",
        Path(tmp_path) / "Example.agda",
        12,
        1,
    )
    assert _is_module_assignment_tsagda090(summary, diagnostic)


def test_real_field_assignment_is_not_suppressed(tmp_path):
    assignment = SimpleNamespace(
        name="Tower.Point",
        line=12,
        node=SimpleNamespace(type="field_assignment"),
    )
    summary = SimpleNamespace(
        ast=SimpleNamespace(
            record_expressions=[SimpleNamespace(assignments=[assignment])]
        )
    )
    diagnostic = Diagnostic(
        "TSAGDA090",
        "qualified record field Tower.Point is invalid in record construction",
        Path(tmp_path) / "Example.agda",
        12,
        1,
    )
    assert not _is_module_assignment_tsagda090(summary, diagnostic)
