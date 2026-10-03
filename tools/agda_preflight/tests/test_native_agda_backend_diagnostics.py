from pathlib import Path
from types import SimpleNamespace

from agda_preflight.checker import Diagnostic
from agda_preflight.evidence import EvidenceLevel
from agda_preflight.scope_backend import (
    AgdaAutoRefineBackend,
    AgdaTypecheckBackend,
    NativeAgdaDiagnostic,
    _append_native_diagnostics,
)


class Completed:
    def __init__(self, *, returncode: int, stdout: str = "", stderr: str = ""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def test_failed_typecheck_retains_native_parse_error(monkeypatch, tmp_path):
    path = tmp_path / "Bad.agda"
    path.write_text("module Bad where\n", encoding="utf-8")
    stderr = (
        f"{path}:10.7: error: [ParseError]\n"
        "in the name foo_9_bar, the part 9 is not valid because it is a literal\n"
        "Agda failed for: Bad.agda\n"
    )
    monkeypatch.setattr(
        "agda_preflight.scope_backend.subprocess.run",
        lambda *args, **kwargs: Completed(returncode=42, stderr=stderr),
    )
    backend = AgdaTypecheckBackend("agda", cwd=tmp_path)
    diagnostics = backend.refine(SimpleNamespace(path=path), [])
    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.code == "TSAGDA390"
    assert diag.severity == "error"
    assert diag.confidence == "agda-confirmed"
    assert diag.evidence == "agda-typechecker"
    assert diag.root_cause == "Agda ParseError"
    assert "part 9 is not valid" in diag.message
    assert backend.failed == 1


def test_successful_typecheck_retains_native_warning(monkeypatch, tmp_path):
    path = tmp_path / "Warn.agda"
    path.write_text("module Warn where\n", encoding="utf-8")
    stderr = (
        f"{path}:3.2-6: warning: -W[no]RewritesNothing\n"
        "`rewrite' did not apply\n"
    )
    monkeypatch.setattr(
        "agda_preflight.scope_backend.subprocess.run",
        lambda *args, **kwargs: Completed(returncode=0, stderr=stderr),
    )
    backend = AgdaTypecheckBackend("agda", cwd=tmp_path)
    diagnostics = backend.refine(SimpleNamespace(path=path), [])
    assert len(diagnostics) == 1
    diag = diagnostics[0]
    assert diag.code == "TSAGDA301"
    assert diag.severity == "warning"
    assert diag.evidence == "agda-typechecker"
    assert "RewritesNothing" in (diag.hint or "")
    assert backend.succeeded == 1


def test_native_diagnostic_upgrades_same_location_index_prediction(tmp_path):
    path = (tmp_path / "Shadow.agda").resolve()
    index = Diagnostic(
        "TSAGDA300",
        "pattern variable pair shadows constructor Cube.pair",
        path,
        10,
        5,
        severity="warning",
        confidence="insufficient-evidence",
        evidence="dashi-index",
        minimum_evidence="agda-scope",
        evidence_sufficient=False,
    )
    native = NativeAgdaDiagnostic(
        code="TSAGDA300",
        message="The pattern variable pair has the same name as the constructor\nCube.pair",
        path=path,
        line=10,
        column=5,
        severity="warning",
        agda_class="PatternShadowsConstructor",
    )
    result = _append_native_diagnostics([index], [native], EvidenceLevel.AGDA_SCOPE)
    assert len(result) == 1
    assert result[0].confidence == "agda-confirmed"
    assert result[0].evidence == "agda-scope"
    assert result[0].evidence_sufficient is True
    assert "PatternShadowsConstructor" in (result[0].hint or "")


def test_cached_failed_scope_probe_replays_native_diagnostics(monkeypatch, tmp_path):
    path = (tmp_path / "Cached.agda").resolve()
    path.write_text("module Cached where\n", encoding="utf-8")
    backend = AgdaAutoRefineBackend("agda", cwd=tmp_path)
    native = NativeAgdaDiagnostic(
        code="TSAGDA390",
        message="bad parse",
        path=path,
        line=4,
        column=2,
        severity="error",
        agda_class="ParseError",
    )

    def fail_scope(_):
        backend.scope.last_native_diagnostics = (native,)
        return False

    monkeypatch.setattr(backend.scope, "_scope_ok", fail_scope)
    assert backend.probe_scope(path) is False

    deferred = Diagnostic(
        "TSAGDA300",
        "possible shadow",
        path,
        2,
        1,
        severity="warning",
        confidence="insufficient-evidence",
        evidence="dashi-index",
        minimum_evidence="agda-scope",
        evidence_sufficient=False,
    )
    result = backend.refine(SimpleNamespace(path=path), [deferred])
    assert any(d.code == "TSAGDA390" and d.message == "bad parse" for d in result)
