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
from agda_preflight.scope_backend import (
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
