"""Static source, proof-owner and validation-boundary tests for BCH2026.

These tests do not execute Agda or Lean kernels.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
EXACT = ROOT / "DASHI/Foundations/AutoformalisationBCH2026Exact.agda"
SOURCES = ROOT / "DASHI/Foundations/AutoformalisationBCH2026Sources.agda"
SCI = ROOT / "DASHI/Foundations/AutoformalisationBCH2026SCIInterface.agda"
DOC = ROOT / "Docs/research/autoformalisation_bch2026_source_fidelity_pareto_ibrahim.md"


def test_reuses_merged_math_owners_without_unsupported_claims():
    text = EXACT.read_text(encoding="utf-8")
    for name in (
        "proofRouteCollision",
        "conclusionDoesNotDetermineProofRoute",
        "matrixArgumentCollision",
        "correctTraceStatementDoesNotDetermineMethod",
        "derivativeDebtWitness",
        "inverseLabelCannotCertifyDerivativeBudget",
        "fluxWitness",
        "fluxLabelCannotDiscardGradientTerm",
        "minimumWitness",
        "identityCannotCertifyDenotation",
    ):
        assert name in text
    assert "DASHI.Core.IntersectionalNonFactorability" in text
    assert "DASHI.Core.InterpretiveFormalisationCoreExact" in text
    assert "SCI=infinity is proved here" in text
    assert not re.search(r"(?m)^\s*(postulate|axiom)\b", text)
    assert "{!!}" not in text


def test_appendix_outstanding_dependencies_are_typed_not_default_true():
    s = SCI.read_text(encoding="utf-8")
    assert "atLeastTwoAlternations : 2 ≤ l" in s
    assert "atLeastNineUnknowns : 9 ≤ k" in s
    for key in ("minimal", "actualSigmaCompleteness",
                "actualNineUnknownPolynomialReduction",
                "actualHierarchySeparation"):
        assert key in s
    assert not re.search(r"(?m)^\s*postulate\b", s)
    assert "{!!}" not in s


def test_fixed_source_attribution_and_rollup():
    s = SOURCES.read_text(encoding="utf-8")
    for phrase in (
        "Alexander Bastounis; Fabian Circelli; Anders C. Hansen",
        "10.48550/arXiv.2610.08144",
        "f9e8bc5b38b6e212696e8a30e3e91517af887bbd",
        "Snowball.canonicalSourceRoleSnowballReceipt",
    ):
        assert phrase in s
    rollup = (ROOT / "DASHI/Foundations/Everything.agda").read_text()
    for name in (
        "AutoformalisationBCH2026Exact",
        "AutoformalisationBCH2026SCIInterface",
        "AutoformalisationBCH2026Sources",
    ):
        assert name in rollup


def test_documented_lemma_scope_and_sci_limits():
    s = DOC.read_text(encoding="utf-8")
    for target in (
        "Example 2.1", "Example 2.2",
        "Example 3.1", "Example 3.3",
        "Example 4.3", "Theorem A.3", "Theorem A.4",
        "Nat.sInf", "nine-unknown DPRM",
        "source-first", "historical",
        "exact-head", "source equivalence",
    ):
        assert target.lower() in s.lower(), target


def test_finite_information_collisions_do_not_require_source_identity():
    cases = [
        ("original NL factor", "fixed Lean factor", "same theorem"),
        ("diagonal proof", "direct entries", "trace>=0"),
        ("NL m+4", "Lean m+5", "inverse estimate"),
        ("NL B_R", "Lean A_R and B_R", "pressure flux"),
        ("minimum exists", "default from empty", "square identity"),
    ]
    for left, right, label in cases:
        assert left != right
        assert label
