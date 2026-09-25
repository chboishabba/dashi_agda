from __future__ import annotations

from pathlib import Path
import re

import pytest

from agda_preflight.checker import Checker, Diagnostic
from agda_preflight.evidence import (
    DIAGNOSTIC_POLICIES,
    EvidenceLevel,
    canonical_code,
    policy_for,
)
from agda_preflight.evidence_cli import main as evidence_main
from agda_preflight.triage_cli import main as triage_main
from agda_preflight.pytest_plugin import CollectedModule, _prime_scope_closure
from agda_preflight.scope_backend import (
    AgdaAutoRefineBackend,
    AgdaScopeCheckBackend,
    AgdaTypecheckBackend,
    CommandScopeCheckBackend,
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



def test_triage_collapses_alias_codes_by_default(tmp_path, capsys):
    import json

    report = tmp_path / "aliases.json"
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
                                "code": "TSAGDA045",
                                "severity": "error",
                                "evidence_sufficient": True,
                                "line": 1,
                                "column": 1,
                                "message": "arity mismatch",
                            },
                            {
                                "code": "TSAGDA110",
                                "severity": "error",
                                "evidence_sufficient": True,
                                "line": 1,
                                "column": 1,
                                "message": "arity mismatch alias",
                            },
                        ],
                    }
                ],
            }
        ),
        encoding="utf-8",
    )

    assert triage_main([str(report)]) == 0
    output = capsys.readouterr().out
    assert "TSAGDA045" in output
    assert "TSAGDA110" not in output

    assert triage_main([str(report), "--raw-codes"]) == 0
    raw_output = capsys.readouterr().out
    assert "TSAGDA045" in raw_output
    assert "TSAGDA110" in raw_output



def test_auto_refine_exposes_oracle_stats(tmp_path):
    path = write_module(tmp_path, "Stats")
    backend = AgdaAutoRefineBackend("agda", typecheck=True)
    backend.scope._scope_ok = lambda _: True
    backend.typecheck._typecheck_ok = lambda _: True

    # Monkeypatched calls bypass subprocess counters, so set representative
    # values directly and assert the public stats contract.
    backend.scope.attempted = 3
    backend.scope.succeeded = 2
    backend.scope.failed = 1
    backend.typecheck.attempted = 1
    backend.typecheck.succeeded = 1
    backend.typecheck.failed = 0

    assert backend.stats() == {
        "scope": {"attempted": 3, "succeeded": 2, "failed": 1},
        "typecheck": {"attempted": 1, "succeeded": 1, "failed": 0},
        "scope_cache": {
            "validated_modules": 0,
            "failed_frontier_modules": 0,
            "aggregate_probe_roots": 0,
            "candidate_modules": 0,
            "partial_progress_modules": 0,
        },
    }




def test_constructor_result_aliases_collapse_to_one_triage_root_cause():
    assert canonical_code("TSAGDA072") == "TSAGDA072"
    assert canonical_code("TSAGDA075") == "TSAGDA072"
    assert canonical_code("TSAGDA114") == "TSAGDA072"


def test_export_name_checks_require_agda_scope_evidence():
    for code in ("TSAGDA021", "TSAGDA023", "TSAGDA025"):
        policy = policy_for(code)
        assert policy.minimum == EvidenceLevel.AGDA_SCOPE
        assert policy.hard_error_allowed is True


def test_scope_success_suppresses_export_name_suspicions(tmp_path):
    write_module(tmp_path, "Lib", "module Lib where\n\nx : Set\nx = Set\n")
    path = write_module(
        tmp_path,
        "Use",
        "module Use where\n\nopen import Lib using (missing)\n",
    )

    backend = AgdaScopeCheckBackend("agda")
    backend._scope_ok = lambda _: True
    checker = Checker(tmp_path, scope_backend=backend)

    hits = checker.check(path)
    assert not any(d.code == "TSAGDA023" for d in hits)

def test_unfolding_sensitive_checks_require_typechecker_evidence():
    for code in (
        "TSAGDA040",
        "TSAGDA045",
        "TSAGDA072",
        "TSAGDA075",
        "TSAGDA110",
        "TSAGDA114",
    ):
        policy = policy_for(code)
        assert policy.minimum == EvidenceLevel.AGDA_TYPECHECKER
        assert policy.hard_error_allowed is False


def test_typing_sensitive_residual_frontier_requires_typechecker():
    for code in (
        "TSAGDA049",
        "TSAGDA052",
        "TSAGDA053",
        "TSAGDA079",
        "TSAGDA104",
        "TSAGDA120",
        "TSAGDA121",
        "TSAGDA122",
        "TSAGDA123",
    ):
        policy = policy_for(code)
        assert policy.minimum == EvidenceLevel.AGDA_TYPECHECKER
        assert policy.hard_error_allowed is False


def test_duplicate_semantic_views_collapse_to_root_causes():
    assert canonical_code("TSAGDA052") == "TSAGDA049"
    assert canonical_code("TSAGDA123") == "TSAGDA120"

def test_scope_backend_preserves_configured_agda_extra_args(tmp_path):
    backend = AgdaScopeCheckBackend(
        "agda",
        cwd=tmp_path,
        extra_args=("-i", ".", "-l", "standard-library"),
    )
    assert backend.extra_args == ("-i", ".", "-l", "standard-library")



def _scope_deferred(path: Path):
    return [
        Diagnostic(
            "TSAGDA113",
            "scope suspicion",
            path,
            1,
            1,
            severity="warning",
            confidence="insufficient-evidence",
            evidence="dashi-index",
            minimum_evidence="agda-scope",
            evidence_sufficient=False,
        )
    ]


def test_scope_closure_without_candidates_uses_zero_probes(tmp_path):
    leaf = write_module(tmp_path, "Zero.Leaf")
    top = write_module(tmp_path, "Zero.Top", "\nimport Zero.Leaf\n")

    backend = AgdaAutoRefineBackend("agda")
    checker = Checker(tmp_path, scope_backend=backend)
    calls = []

    def forbidden(path, *, aggregate_root=False):
        calls.append(Path(path).resolve())
        raise AssertionError("no scope probe expected without candidates")

    backend.probe_scope = forbidden
    collected = [
        CollectedModule("Zero.Leaf", leaf),
        CollectedModule("Zero.Top", top),
    ]

    _prime_scope_closure(checker, top, collected)

    assert calls == []
    assert backend.stats()["scope_cache"]["candidate_modules"] == 0


def test_scope_closure_root_success_uses_one_probe(tmp_path):
    leaf = write_module(tmp_path, "A.Leaf")
    middle = write_module(
        tmp_path,
        "A.Middle",
        "\nimport A.Leaf\n",
    )
    top = write_module(
        tmp_path,
        "A.Top",
        "\nimport A.Middle\n",
    )

    backend = AgdaAutoRefineBackend("agda")
    calls = []

    def probe(path, *, aggregate_root=False):
        key = Path(path).resolve()
        calls.append((key, aggregate_root))
        backend._scope_validated.add(key)
        if aggregate_root:
            backend._scope_probe_roots.add(key)
        return True

    backend.probe_scope = probe
    checker = Checker(tmp_path, scope_backend=backend)
    checker.structural_check = lambda path: _scope_deferred(Path(path))
    collected = [
        CollectedModule("A.Leaf", leaf),
        CollectedModule("A.Middle", middle),
        CollectedModule("A.Top", top),
    ]

    _prime_scope_closure(checker, top, collected)

    assert [path for path, _ in calls] == [top.resolve()]
    assert backend.scope_validated(leaf)
    assert backend.scope_validated(middle)
    assert backend.scope_validated(top)


def test_scope_closure_descends_only_failed_subtrees(tmp_path):
    left_leaf = write_module(tmp_path, "A.LeftLeaf")
    left = write_module(
        tmp_path,
        "A.Left",
        "\nimport A.LeftLeaf\n",
    )
    right_leaf = write_module(tmp_path, "A.RightLeaf")
    right = write_module(
        tmp_path,
        "A.Right",
        "\nimport A.RightLeaf\n",
    )
    top = write_module(
        tmp_path,
        "A.Top",
        "\nimport A.Left\nimport A.Right\n",
    )

    backend = AgdaAutoRefineBackend("agda")
    outcomes = {
        top.resolve(): False,
        left.resolve(): True,
        right.resolve(): False,
        right_leaf.resolve(): True,
    }
    calls = []

    def probe(path, *, aggregate_root=False):
        key = Path(path).resolve()
        calls.append(key)
        ok = outcomes[key]
        if ok:
            backend._scope_validated.add(key)
        else:
            backend._scope_failed.add(key)
        if aggregate_root:
            backend._scope_probe_roots.add(key)
        return ok

    backend.probe_scope = probe
    checker = Checker(tmp_path, scope_backend=backend)
    candidate_paths = {left_leaf.resolve(), right_leaf.resolve()}
    checker.structural_check = lambda path: (
        _scope_deferred(Path(path))
        if Path(path).resolve() in candidate_paths
        else []
    )
    collected = [
        CollectedModule("A.LeftLeaf", left_leaf),
        CollectedModule("A.Left", left),
        CollectedModule("A.RightLeaf", right_leaf),
        CollectedModule("A.Right", right),
        CollectedModule("A.Top", top),
    ]

    _prime_scope_closure(checker, top, collected)

    assert calls == [
        top.resolve(),
        left.resolve(),
        right.resolve(),
        right_leaf.resolve(),
    ]
    assert backend.scope_validated(left_leaf)
    assert backend.scope_validated(left)
    assert backend.scope_validated(right_leaf)
    assert backend.scope_failed(right)
    assert backend.scope_failed(top)
    assert backend.stats()["scope_cache"]["candidate_modules"] == 2


def test_scope_closure_skips_irrelevant_failed_subtree(tmp_path):
    left = write_module(tmp_path, "P.Left")
    right = write_module(tmp_path, "P.Right")
    top = write_module(
        tmp_path,
        "P.Top",
        "\nimport P.Left\nimport P.Right\n",
    )

    backend = AgdaAutoRefineBackend("agda")
    calls = []

    def probe(path, *, aggregate_root=False):
        key = Path(path).resolve()
        calls.append(key)
        if key == top.resolve():
            backend._scope_failed.add(key)
            return False
        if key == left.resolve():
            backend._scope_validated.add(key)
            return True
        raise AssertionError("irrelevant right subtree must not be probed")

    backend.probe_scope = probe
    checker = Checker(tmp_path, scope_backend=backend)
    checker.structural_check = lambda path: (
        _scope_deferred(Path(path))
        if Path(path).resolve() == left.resolve()
        else []
    )
    collected = [
        CollectedModule("P.Left", left),
        CollectedModule("P.Right", right),
        CollectedModule("P.Top", top),
    ]

    _prime_scope_closure(checker, top, collected)

    assert calls == [top.resolve(), left.resolve()]
    assert backend.scope_validated(left)
    assert not backend.scope_known(right)


def test_failed_scope_frontier_is_not_reprobed_during_refine(tmp_path):
    path = write_module(tmp_path, "FailedFrontier")
    backend = AgdaAutoRefineBackend("agda")
    backend._scope_failed.add(path.resolve())

    def forbidden(_):
        raise AssertionError("cached failed scope frontier must not be reprobed")

    backend.scope._scope_ok = forbidden
    checker = Checker(tmp_path, scope_backend=backend)
    summary = checker.parse_summary(path)
    diagnostic = Diagnostic(
        "TSAGDA113",
        "scope suspicion",
        path,
        2,
        1,
        severity="error",
    )

    [result] = checker._apply_evidence_policy(summary, [diagnostic])
    assert result.severity == "warning"
    assert result.evidence_sufficient is False



def test_command_scope_runner_substitutes_file_placeholder(tmp_path):
    path = write_module(tmp_path, "Runner.Placeholder")
    backend = CommandScopeCheckBackend(
        ["shadow-check", "--only-scope-checking", "{file}"],
        cwd=tmp_path,
    )

    assert backend._argv(path) == [
        "shadow-check",
        "--only-scope-checking",
        str(path.resolve()),
    ]


def test_command_scope_runner_appends_file_without_placeholder(tmp_path):
    path = write_module(tmp_path, "Runner.Append")
    backend = CommandScopeCheckBackend(
        ["shadow-check", "--only-scope-checking"],
        cwd=tmp_path,
    )

    assert backend._argv(path) == [
        "shadow-check",
        "--only-scope-checking",
        str(path.resolve()),
    ]


def test_auto_refine_can_use_exit_code_scope_runner(tmp_path):
    backend = AgdaAutoRefineBackend(
        "unused-agda",
        cwd=tmp_path,
        scope_command="shadow-check --only-scope-checking {file}",
    )

    assert isinstance(backend.scope, CommandScopeCheckBackend)
    assert backend.scope.command == (
        "shadow-check",
        "--only-scope-checking",
        "{file}",
    )



def test_command_scope_runner_extracts_agda_checked_modules():
    output = """Logging Agda output to: /tmp/log
Checking: DASHI/Everything.agda
Checking DASHI.Core.Prelude (/shadow/DASHI/Core/Prelude.agda).
Checking DASHI.Algebra.Foo (/shadow/DASHI/Algebra/Foo.agda).
Checking DASHI.Biology.Broken (/shadow/DASHI/Biology/Broken.agda).
"""
    modules = CommandScopeCheckBackend._checked_modules(output)
    assert modules == (
        "DASHI.Core.Prelude",
        "DASHI.Algebra.Foo",
        "DASHI.Biology.Broken",
    )


def test_failed_command_scope_probe_excludes_last_checked_module(tmp_path, monkeypatch):
    path = write_module(tmp_path, "Root")
    backend = CommandScopeCheckBackend(["shadow-check", "{file}"], cwd=tmp_path)

    class Completed:
        returncode = 1
        stdout = (
            "Checking A.Good (/shadow/A/Good.agda).\n"
            "Checking A.AlsoGood (/shadow/A/AlsoGood.agda).\n"
            "Checking A.Broken (/shadow/A/Broken.agda).\n"
        )
        stderr = "type mismatch"

    monkeypatch.setattr(
        "agda_preflight.scope_backend.subprocess.run",
        lambda *args, **kwargs: Completed(),
    )

    assert backend._scope_ok(path) is False
    assert backend.last_checked_modules == (
        "A.Good",
        "A.AlsoGood",
        "A.Broken",
    )
    assert backend.last_partial_validated_modules == (
        "A.Good",
        "A.AlsoGood",
    )
    assert "A.Broken" not in backend.partial_validated_modules


def test_timeout_scope_probe_recovers_completed_prefix(tmp_path, monkeypatch):
    path = write_module(tmp_path, "RootTimeout")
    backend = CommandScopeCheckBackend(["shadow-check", "{file}"], cwd=tmp_path)

    def timeout(*args, **kwargs):
        raise __import__("subprocess").TimeoutExpired(
            cmd=args[0],
            timeout=kwargs.get("timeout", 1),
            output=(
                "Checking A.One (/shadow/A/One.agda).\n"
                "Checking A.Two (/shadow/A/Two.agda).\n"
            ),
            stderr="",
        )

    monkeypatch.setattr(
        "agda_preflight.scope_backend.subprocess.run",
        timeout,
    )

    assert backend._scope_ok(path) is False
    assert backend.last_partial_validated_modules == ("A.One",)


def test_partial_scope_progress_bulk_certifies_before_fallback(tmp_path):
    good = write_module(tmp_path, "Q.Good")
    broken = write_module(tmp_path, "Q.Broken")
    top = write_module(
        tmp_path,
        "Q.Top",
        "\nimport Q.Good\nimport Q.Broken\n",
    )

    backend = AgdaAutoRefineBackend(
        "unused",
        scope_command="shadow-check {file}",
    )
    calls = []

    def probe(path, *, aggregate_root=False):
        key = Path(path).resolve()
        calls.append(key)
        if key == top.resolve():
            backend._scope_failed.add(key)
            backend.scope.last_partial_validated_modules = ("Q.Good", "Q.Broken")
            # Simulate a conservative failing prefix: plugin should map these
            # names, but the failing module must not appear in real backend
            # output's partial list. Keep only Good here.
            backend.scope.last_partial_validated_modules = ("Q.Good",)
            return False
        if key == broken.resolve():
            backend._scope_failed.add(key)
            backend.scope.last_partial_validated_modules = ()
            return False
        raise AssertionError(f"unexpected probe: {key}")

    backend.probe_scope = probe
    checker = Checker(tmp_path, scope_backend=backend)
    checker.structural_check = lambda path: _scope_deferred(Path(path))
    collected = [
        CollectedModule("Q.Good", good),
        CollectedModule("Q.Broken", broken),
        CollectedModule("Q.Top", top),
    ]

    _prime_scope_closure(checker, top, collected)

    assert backend.scope_validated(good)
    assert calls == [top.resolve(), broken.resolve()]
