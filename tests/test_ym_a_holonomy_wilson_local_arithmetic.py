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
    / "YMAHolonomyWilsonLocalArithmetic.agda"
)

TRUE_FLAGS = (
    "wilsonArithmeticRecorded",
    "qInterpretationAcceptedAsInput",
)

FALSE_FLAGS = (
    "holonomySeparationTheoremProved",
    "finiteDominationTheoremProved",
    "continuumTransferProved",
    "clayYangMillsPromoted",
)


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


@pytest.fixture(scope="module")
def receipt_text() -> str:
    assert RECEIPT.is_file(), f"missing receipt: {RECEIPT.relative_to(REPO_ROOT)}"
    return RECEIPT.read_text(encoding="utf-8")


def test_ym_a_holonomy_wilson_local_arithmetic_typechecks_no_libraries() -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_ym_a_holonomy_wilson_local_arithmetic_records_authority_rows(
    receipt_text: str,
) -> None:
    required_names = (
        "AuthorityRationalRow",
        "qApprox",
        "negLogQApprox",
        "SWminOverN",
        "c2SU2",
        "c2SU3",
        "SWminSU2",
        "SWminSU3",
        "qInterpretationBoundaryStatement",
    )
    for name in required_names:
        assert re.search(rf"\b{re.escape(name)}\b", receipt_text), name

    required_numbers = (
        "23178189475262734",
        "100000000000000000",
        "1462",
        "2924",
        "4386",
        "1000",
    )
    for number in required_numbers:
        assert number in receipt_text

    assert "SWmin/N = negLogQApprox = 1462 / 1000" in receipt_text
    assert "convention/authority input accepted by this receipt" in receipt_text
    assert "not an analytic logarithm computation" in receipt_text


def test_ym_a_holonomy_wilson_local_arithmetic_fail_closed_flags(
    receipt_text: str,
) -> None:
    for name in TRUE_FLAGS:
        assert agda_bool_assignment(receipt_text, name, True), name
        assert re.search(
            rf"\b{name}[A-Za-z0-9_']*\s*:\s*{re.escape(name)}\s*≡\s*true",
            receipt_text,
        ), f"missing true proof for {name}"

    for name in FALSE_FLAGS:
        assert agda_bool_assignment(receipt_text, name, False), name
        assert re.search(
            rf"\b[A-Za-z][A-Za-z0-9_']*\s*:\s*{re.escape(name)}\s*≡\s*false",
            receipt_text,
        ), f"missing false proof for {name}"

    assert not re.search(
        r"\b(?:holonomySeparationTheoremProved|"
        r"finiteDominationTheoremProved|"
        r"continuumTransferProved|"
        r"clayYangMillsPromoted)\s*=\s*true\b",
        receipt_text,
    )


def test_ym_a_holonomy_wilson_local_arithmetic_orcslpgf_surface(
    receipt_text: str,
) -> None:
    for key in ("O:", "R:", "C:", "S:", "L:", "P:", "G:", "F:"):
        assert key in receipt_text

    assert "canonicalYMAHolonomyWilsonLocalArithmeticORCSLPGF" in receipt_text


def test_ym_a_holonomy_wilson_local_arithmetic_no_forbidden_scaffolding(
    receipt_text: str,
) -> None:
    forbidden = (
        r"\bpostulate\b",
        r"\bTODO\b",
        r"\bSKIP\b",
        r"\bskeleton\b",
        r"\?",
        r"\{!\s*.*?\s*!\}",
    )
    for pattern in forbidden:
        assert not re.search(pattern, receipt_text, flags=re.DOTALL), pattern
