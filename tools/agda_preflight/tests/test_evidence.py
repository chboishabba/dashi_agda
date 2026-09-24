from __future__ import annotations

from pathlib import Path
import re

import pytest

from agda_preflight.checker import Checker, Diagnostic
from agda_preflight.evidence import (
    DIAGNOSTIC_POLICIES,
    EvidenceLevel,
    policy_for,
)
from agda_preflight.evidence_cli import main as evidence_main
from agda_preflight.triage_cli import main as triage_main
from agda_preflight.scope_backend import (
    AgdaAutoRefineBackend,
    AgdaScopeCheckBackend,
    AgdaTypecheckBackend,
    ExternalScopeBackend,
    ScopeRefinement,
    diagnostic_key,
)


def write_module(root: Path, module: str, body: str = "") -> Path:
    path = root.joinpath(*module.split(".")).with_suffix(".agda")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(f"module {module} where\n{body}", encoding="utf-8")
    return path


def test_every_documented_diagnostic_has_explicit_evidence_policy():
    readme = Path(__file__).parents[1] / "README.md"
    documented = set(re.findall(r"TSAGDA\d{3}", readme.read_text(encoding="utf-8")))
    assert documented
    assert documented == set(DIAGNOSTIC_POLICIES)


def test_unclassified_diagnostic_is_programming_error():
    with pytest.raises(KeyError):
        policy_for("TSAGDA999")


def test_scope_required_structural_error_is_downgraded(tmp_path):
    path = write_module(tmp_path, "Evidence")
    checker = Checker(tmp_path)
    summary = checker.parse_summary(path)
    diagnostic = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
        confidence="high",
    )

    [result] = checker._apply_evidence_policy(summary, [diagnostic])

    assert result.severity == "warning"
    assert result.confidence == "insufficient-evidence"
    assert result.evidence == "dashi-index"
    assert result.minimum_evidence == "agda-scope"
    assert result.evidence_sufficient is False


def test_scope_confirmation_restores_hard_error(tmp_path):
    path = write_module(tmp_path, "EvidenceConfirm")
    diagnostic = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
        confidence="high",
    )

    backend = ExternalScopeBackend(["unused"])
    backend._run = lambda _: ScopeRefinement({diagnostic_key(diagnostic)}, set())
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    [result] = checker._apply_evidence_policy(summary, [diagnostic])

    assert result.severity == "error"
    assert result.confidence == "scope-confirmed"
    assert result.evidence == "agda-scope"
    assert result.minimum_evidence == "agda-scope"
    assert result.evidence_sufficient is True


def test_scope_suppression_removes_structural_suspicion(tmp_path):
    path = write_module(tmp_path, "EvidenceSuppress")
    diagnostic = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
        confidence="high",
    )

    backend = ExternalScopeBackend(["unused"])
    backend._run = lambda _: ScopeRefinement(set(), {diagnostic_key(diagnostic)})
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    assert checker._apply_evidence_policy(summary, [diagnostic]) == []


def test_tree_only_error_remains_hard_without_scope_backend(tmp_path):
    path = write_module(tmp_path, "TreeEvidence")
    checker = Checker(tmp_path)
    summary = checker.parse_summary(path)
    diagnostic = Diagnostic(
        "TSAGDA012",
        "interaction hole",
        path,
        2,
        1,
        severity="error",
        confidence="high",
    )

    [result] = checker._apply_evidence_policy(summary, [diagnostic])

    assert result.severity == "error"
    assert result.evidence == "tree-sitter"
    assert result.minimum_evidence == "tree-sitter"
    assert result.evidence_sufficient is True



def test_native_scope_success_suppresses_scope_only_diagnostics(tmp_path):
    path = write_module(tmp_path, "NativeScope")
    backend = AgdaScopeCheckBackend("agda")
    backend._scope_ok = lambda _: True
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    scope_diag = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
    )
    typing_diag = Diagnostic(
        "TSAGDA041",
        "function may be under-applied",
        path,
        3,
        1,
        severity="error",
    )

    results = checker._apply_evidence_policy(summary, [scope_diag, typing_diag])

    assert [d.code for d in results] == ["TSAGDA041"]
    assert results[0].severity == "warning"
    assert results[0].minimum_evidence == "agda-typechecker"
    assert results[0].evidence_sufficient is False


def test_native_scope_failure_does_not_confirm_any_suspicion(tmp_path):
    path = write_module(tmp_path, "NativeScopeFailure")
    backend = AgdaScopeCheckBackend("agda")
    backend._scope_ok = lambda _: False
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    diagnostic = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
    )

    [result] = checker._apply_evidence_policy(summary, [diagnostic])

    assert result.severity == "warning"
    assert result.confidence == "insufficient-evidence"
    assert result.evidence_sufficient is False


def test_typing_dependent_rules_require_typechecker_evidence():
    assert policy_for("TSAGDA041").minimum == EvidenceLevel.AGDA_TYPECHECKER
    assert policy_for("TSAGDA076").minimum == EvidenceLevel.AGDA_TYPECHECKER



def test_full_typecheck_success_suppresses_scope_and_typing_suspicions(tmp_path):
    path = write_module(tmp_path, "TypecheckOracle")
    backend = AgdaTypecheckBackend("agda")
    backend._typecheck_ok = lambda _: True
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    diagnostics = [
        Diagnostic(
            "TSAGDA113",
            "identifier may be unbound",
            path,
            2,
            1,
            severity="error",
        ),
        Diagnostic(
            "TSAGDA041",
            "function may be under-applied",
            path,
            3,
            1,
            severity="error",
        ),
        Diagnostic(
            "TSAGDA204",
            "Exact module contains a proof placeholder",
            path,
            4,
            1,
            severity="error",
        ),
    ]

    results = checker._apply_evidence_policy(summary, diagnostics)

    assert [d.code for d in results] == ["TSAGDA204"]


def test_full_typecheck_failure_does_not_suppress_structural_suspicions(tmp_path):
    path = write_module(tmp_path, "TypecheckOracleFailure")
    backend = AgdaTypecheckBackend("agda")
    backend._typecheck_ok = lambda _: False
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    diagnostics = [
        Diagnostic(
            "TSAGDA113",
            "identifier may be unbound",
            path,
            2,
            1,
            severity="error",
        ),
        Diagnostic(
            "TSAGDA041",
            "function may be under-applied",
            path,
            3,
            1,
            severity="error",
        ),
    ]

    results = checker._apply_evidence_policy(summary, diagnostics)

    assert [d.code for d in results] == ["TSAGDA113", "TSAGDA041"]
    assert all(d.severity == "warning" for d in results)
    assert all(d.evidence_sufficient is False for d in results)



def test_evidence_cli_filters_by_minimum_layer(capsys):
    assert evidence_main(["--level", "agda-scope"]) == 0
    output = capsys.readouterr().out
    assert "agda-scope" in output
    assert "TSAGDA113" in output
    assert "TSAGDA041" not in output



def test_auto_refine_does_not_run_agda_without_deferred_findings(tmp_path):
    path = write_module(tmp_path, "AutoNoop")
    backend = AgdaAutoRefineBackend("agda", typecheck=True)

    def forbidden(_):
        raise AssertionError("Agda should not run without deferred findings")

    backend.scope._scope_ok = forbidden
    backend.typecheck._typecheck_ok = forbidden

    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)
    diagnostic = Diagnostic(
        "TSAGDA204",
        "trust-policy finding",
        path,
        2,
        1,
        severity="error",
    )

    [result] = checker._apply_evidence_policy(summary, [diagnostic])
    assert result.code == "TSAGDA204"


def test_auto_refine_runs_scope_only_when_scope_evidence_is_needed(tmp_path):
    path = write_module(tmp_path, "AutoScope")
    backend = AgdaAutoRefineBackend("agda", typecheck=False)
    calls = {"scope": 0}

    def scope_ok(_):
        calls["scope"] += 1
        return True

    backend.scope._scope_ok = scope_ok
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)
    diagnostic = Diagnostic(
        "TSAGDA113",
        "identifier may be unbound",
        path,
        2,
        1,
        severity="error",
    )

    assert checker._apply_evidence_policy(summary, [diagnostic]) == []
    assert calls == {"scope": 1}


def test_auto_refine_scope_failure_skips_full_typecheck(tmp_path):
    path = write_module(tmp_path, "AutoScopeFail")
    backend = AgdaAutoRefineBackend("agda", typecheck=True)
    calls = {"scope": 0, "typecheck": 0}

    def scope_fail(_):
        calls["scope"] += 1
        return False

    def typecheck_forbidden(_):
        calls["typecheck"] += 1
        raise AssertionError("typecheck should not run after scope failure")

    backend.scope._scope_ok = scope_fail
    backend.typecheck._typecheck_ok = typecheck_forbidden
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    diagnostics = [
        Diagnostic("TSAGDA113", "scope suspicion", path, 2, 1, severity="error"),
        Diagnostic("TSAGDA041", "typing suspicion", path, 3, 1, severity="error"),
    ]
    results = checker._apply_evidence_policy(summary, diagnostics)

    assert [d.code for d in results] == ["TSAGDA113", "TSAGDA041"]
    assert calls == {"scope": 1, "typecheck": 0}


def test_auto_refine_typechecks_only_surviving_typechecker_findings(tmp_path):
    path = write_module(tmp_path, "AutoTypecheck")
    backend = AgdaAutoRefineBackend("agda", typecheck=True)
    calls = {"scope": 0, "typecheck": 0}

    def scope_ok(_):
        calls["scope"] += 1
        return True

    def typecheck_ok(_):
        calls["typecheck"] += 1
        return True

    backend.scope._scope_ok = scope_ok
    backend.typecheck._typecheck_ok = typecheck_ok
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)

    diagnostics = [
        Diagnostic("TSAGDA113", "scope suspicion", path, 2, 1, severity="error"),
        Diagnostic("TSAGDA041", "typing suspicion", path, 3, 1, severity="error"),
        Diagnostic("TSAGDA204", "trust-policy finding", path, 4, 1, severity="error"),
    ]
    results = checker._apply_evidence_policy(summary, diagnostics)

    assert [d.code for d in results] == ["TSAGDA204"]
    assert calls == {"scope": 1, "typecheck": 1}



def test_triage_cli_summarizes_hard_and_deferred_findings(tmp_path, capsys):
    import json

    report = tmp_path / "report.json"
    report.write_text(
        json.dumps(
            {
                "summary": {},
                "modules": [
                    {
                        "nodeid": "A.agda::A",
                        "outcome": "failed",
                        "diagnostics": [
                            {
                                "code": "TSAGDA060",
                                "severity": "error",
                                "evidence_sufficient": True,
                                "line": 10,
                                "column": 2,
                                "message": "unknown field",
                            },
                            {
                                "code": "TSAGDA113",
                                "severity": "warning",
                                "evidence_sufficient": False,
                                "line": 11,
                                "column": 3,
                                "message": "scope suspicion",
                            },
                        ],
                    },
                    {
                        "nodeid": "B.agda::B",
                        "outcome": "failed",
                        "diagnostics": [
                            {
                                "code": "TSAGDA060",
                                "severity": "error",
                                "evidence_sufficient": True,
                                "line": 4,
                                "column": 1,
                                "message": "unknown field",
                            }
                        ],
                    },
                ],
            }
        ),
        encoding="utf-8",
    )

    assert triage_main([str(report), "--top", "5"]) == 0
    hard_output = capsys.readouterr().out
    assert "TSAGDA060" in hard_output
    assert "2" in hard_output
    assert "A" in hard_output
    assert "B" in hard_output

    assert triage_main([str(report), "--deferred"]) == 0
    deferred_output = capsys.readouterr().out
    assert "TSAGDA113" in deferred_output
    assert "scope suspicion" in deferred_output
