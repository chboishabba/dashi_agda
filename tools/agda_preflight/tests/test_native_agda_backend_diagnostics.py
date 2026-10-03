from pathlib import Path
from types import SimpleNamespace

from agda_preflight.scope_backend import AgdaTypecheckBackend


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
