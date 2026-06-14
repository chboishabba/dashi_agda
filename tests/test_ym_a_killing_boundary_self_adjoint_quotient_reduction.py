from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMAKillingBoundarySelfAdjointQuotientReduction.agda"
)

CHILD_IMPORTS = (
    "DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic",
    "DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic",
    "DASHI.Physics.Closure.YMAFiniteDominationArithmeticComposite",
)

TRUE_BOOKKEEPING_FLAGS = (
    "localKillingBoundaryArithmeticConsumed",
    "localHolonomyWilsonArithmeticConsumed",
    "finiteDominationArithmeticCompositeConsumed",
)

FALSE_THEOREM_FLAGS = (
    "domainClosureTheoremProved",
    "boundaryFluxTheoremProved",
    "quotientSelfAdjointnessTheoremProved",
    "selfAdjointQuotientHamiltonianProved",
    "h3aProved",
    "clayYangMillsPromoted",
    "terminalPromotionProved",
)

ROUTE_TEXT = (
    "opposite-face involution",
    "gauge invariance",
    "finite-dimensional symmetric quotient matrices are self-adjoint",
    "Bochner positivity, King lower-bound arithmetic, and Wilson holonomy rows",
)

BLOCKER_TEXT = (
    "domain closure theorem remains false",
    "boundary flux theorem remains false",
    "quotient self-adjointness theorem remains false",
    "H3a remains false",
    "Clay Yang-Mills and terminal promotion remain false",
)


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def module_path(module: str) -> Path:
    return REPO_ROOT / Path(*module.split(".")).with_suffix(".agda")


@pytest.fixture(scope="module")
def module_text() -> str:
    assert MODULE.is_file(), "missing self-adjoint quotient reduction receipt"
    return MODULE.read_text(encoding="utf-8")


def test_self_adjoint_quotient_reduction_typechecks_no_libraries(
    module_text: str,
) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    missing_children = [
        module for module in CHILD_IMPORTS if not module_path(module).is_file()
    ]
    if missing_children:
        pytest.skip(
            "child local arithmetic modules are not present yet: "
            + ", ".join(missing_children)
        )

    result = subprocess.run(
        [agda, "--no-libraries", str(MODULE.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_self_adjoint_quotient_reduction_consumes_local_arithmetic(
    module_text: str,
) -> None:
    for module in CHILD_IMPORTS:
        assert re.search(rf"^import\s+{re.escape(module)}\b", module_text, re.MULTILINE)

    for name in TRUE_BOOKKEEPING_FLAGS:
        assert agda_bool_assignment(module_text, name, True), name

    for consumed_name in (
        "KillingBoundaryArithmetic.arithmeticRecorded",
        "KillingBoundaryArithmetic.kingAuthorityAcceptedAsArithmeticInput",
        "HolonomyWilsonArithmetic.wilsonArithmeticRecorded",
        "HolonomyWilsonArithmetic.qInterpretationAcceptedAsInput",
        "FiniteDominationArithmeticComposite.c1PositiveArithmetic",
        "FiniteDominationArithmeticComposite.c2PositiveArithmetic",
        "FiniteDominationArithmeticComposite.localArithmeticObstructionAbsent",
    ):
        assert consumed_name in module_text


def test_self_adjoint_quotient_reduction_records_route_without_promotion(
    module_text: str,
) -> None:
    for required in ROUTE_TEXT:
        assert required in module_text, required

    assert "boundaryReductionRouteLengthIs6" in module_text
    assert re.search(r"\bboundaryReductionRouteLengthIs6\s*=\s*refl\b", module_text)

    for required in BLOCKER_TEXT:
        assert required in module_text, required

    assert "boundaryReductionBlockerCountIs5" in module_text
    assert re.search(r"\bboundaryReductionBlockerCountIs5\s*=\s*refl\b", module_text)


def test_self_adjoint_quotient_reduction_theorem_blockers_stay_false(
    module_text: str,
) -> None:
    for name in FALSE_THEOREM_FLAGS:
        assert agda_bool_assignment(module_text, name, False), name
        assert not agda_bool_assignment(module_text, name, True), name

    for imported_false in (
        "KillingBoundaryArithmetic.domainClosureProved",
        "KillingBoundaryArithmetic.boundaryFluxCancellationProved",
        "HolonomyWilsonArithmetic.finiteDominationTheoremProved",
        "FiniteDominationArithmeticComposite.finiteDominationTheoremPromoted",
        "FiniteDominationArithmeticComposite.selfAdjointQuotientHamiltonianProved",
        "FiniteDominationArithmeticComposite.h3aTransferProved",
        "FiniteDominationArithmeticComposite.clayYangMillsPromoted",
    ):
        assert imported_false in module_text


def test_self_adjoint_quotient_reduction_has_no_positive_theorem_promotion(
    module_text: str,
) -> None:
    positive_promotion = re.compile(
        r"\b[A-Za-z][A-Za-z0-9_']*(?:Promoted|Promotion|Solved|Proved|Theorem)"
        r"[A-Za-z0-9_']*\s*=\s*true\b"
    )
    offenders = [
        match.group(0)
        for match in positive_promotion.finditer(module_text)
        if "ArithmeticConsumed" not in match.group(0)
    ]
    assert offenders == []


def test_self_adjoint_quotient_reduction_has_orcslpgf_summary(
    module_text: str,
) -> None:
    for label in ("O :", "R :", "C :", "S :", "L :", "P :", "G :", "F :"):
        assert label in module_text
