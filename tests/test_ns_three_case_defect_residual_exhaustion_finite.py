from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSThreeCaseDefectResidualExhaustionFinite.agda"
)

CASES = ("spread", "wedgeCollapse", "avoidSigma")
FINITE_TRUE_FLAGS = (
    "allCasesClosedFinite",
    "noPersistentPositiveResidualFinite",
)
OPEN_FALSE_FLAGS = (
    "MicrolocalAlignmentConcentrationLemma",
    "AngularDegeneracyPressureCommutatorGain",
    "MechanismExhaustionForFullClayNS",
    "clayNavierStokesPromoted",
)


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), f"missing receipt: {RECEIPT.relative_to(REPO_ROOT)}"
    return RECEIPT.read_text(encoding="utf-8")


def test_ns_three_case_finite_receipt_typechecks_with_agda() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_ns_three_case_finite_encodes_cases_and_residual_bounds(
    receipt_text: str,
) -> None:
    text = receipt_text

    assert re.search(r"\bdata\s+Case\s*:\s*Set\s+where", text)
    for case in CASES:
        assert re.search(rf"\b{case}\s*:\s*Case\b", text), case
        assert re.search(
            rf"\bresidualNumerator\s+{case}\s*=\s*\d+\b", text
        ), case

    assert "residualBaseline" in text
    assert "residualNumerator≤baseline" in text
    assert "FiniteResidualWitness" in text
    assert "negativeOrZeroResidualWitness" in text
    assert "persistentPositiveResidualIsFalse" in text


def test_ns_three_case_finite_closure_flags(receipt_text: str) -> None:
    for name in FINITE_TRUE_FLAGS:
        assert agda_bool_assignment(receipt_text, name, True), name
        assert re.search(
            rf"\b{name}[A-Za-z0-9_']*\s*:\s*{re.escape(name)}\s*≡\s*true",
            receipt_text,
        ), f"missing true proof for {name}"


def test_ns_three_case_finite_open_analytic_flags_fail_closed(
    receipt_text: str,
) -> None:
    for name in OPEN_FALSE_FLAGS:
        assert agda_bool_assignment(receipt_text, name, False), name
        assert re.search(
            rf"\b[A-Za-z][A-Za-z0-9_']*\s*:\s*{re.escape(name)}\s*≡\s*false",
            receipt_text,
        ), f"missing false proof for {name}"

    assert not re.search(
        r"\b(?:MicrolocalAlignmentConcentrationLemma|"
        r"AngularDegeneracyPressureCommutatorGain|"
        r"MechanismExhaustionForFullClayNS|"
        r"clayNavierStokesPromoted)\s*=\s*true\b",
        receipt_text,
    )


def test_ns_three_case_finite_no_postulate_hole_or_skeleton(
    receipt_text: str,
) -> None:
    forbidden = (
        r"\bpostulate\b",
        r"\b{-#\s*TERMINATING\s*#-}",
        r"\b{-#\s*NON_TERMINATING\s*#-}",
        r"\bTODO\b",
        r"\bSKIP\b",
        r"\bskeleton\b",
        r"\?",
        r"\{!\s*.*?\s*!\}",
    )
    for pattern in forbidden:
        assert not re.search(pattern, receipt_text, flags=re.DOTALL), pattern


def test_ns_three_case_finite_orcslpgf_surface(receipt_text: str) -> None:
    for key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert key in receipt_text

    assert "canonicalNSThreeCaseFiniteORCSLPGF" in receipt_text
