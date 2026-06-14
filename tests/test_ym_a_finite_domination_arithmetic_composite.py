from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
COMPOSITE = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "YMAFiniteDominationArithmeticComposite.agda"
)

CHILD_IMPORTS = (
    "DASHI.Physics.Closure.YMAKillingBoundaryLocalArithmetic",
    "DASHI.Physics.Closure.YMAHolonomyWilsonLocalArithmetic",
)

TRUE_FLAGS = (
    "c1PositiveArithmetic",
    "c2PositiveArithmetic",
    "localArithmeticObstructionAbsent",
)

FALSE_THEOREM_FLAGS = (
    "finiteDominationTheoremPromoted",
    "selfAdjointQuotientHamiltonianProved",
    "h3aTransferProved",
    "clayYangMillsPromoted",
)

THEOREM_BLOCKERS = (
    "domain closure",
    "boundary flux cancellation",
    "quotient self-adjointness",
    "H3a continuum transfer",
)


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def module_path(module: str) -> Path:
    return REPO_ROOT / Path(*module.split(".")).with_suffix(".agda")


@pytest.fixture(scope="module")
def composite_text() -> str:
    assert COMPOSITE.is_file(), "missing YM-A finite domination arithmetic composite"
    return COMPOSITE.read_text(encoding="utf-8")


def test_yma_finite_domination_arithmetic_composite_typechecks_with_agda(
    composite_text: str,
) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    missing_children = [
        module
        for module in CHILD_IMPORTS
        if not module_path(module).is_file()
    ]
    if missing_children:
        pytest.skip(
            "child local arithmetic modules are not present yet: "
            + ", ".join(missing_children)
        )

    result = subprocess.run(
        [agda, "--no-libraries", str(COMPOSITE.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_yma_finite_domination_arithmetic_composite_imports_children(
    composite_text: str,
) -> None:
    for module in CHILD_IMPORTS:
        assert re.search(rf"^import\s+{re.escape(module)}\b", composite_text, re.MULTILINE)


def test_yma_finite_domination_arithmetic_flags_are_closure_only(
    composite_text: str,
) -> None:
    for name in TRUE_FLAGS:
        assert agda_bool_assignment(composite_text, name, True), name

    for name in FALSE_THEOREM_FLAGS:
        assert agda_bool_assignment(composite_text, name, False), name
        assert not agda_bool_assignment(composite_text, name, True), name


def test_yma_finite_domination_arithmetic_lists_expected_theorem_blockers(
    composite_text: str,
) -> None:
    for blocker in THEOREM_BLOCKERS:
        assert blocker in composite_text

    for constructor in (
        "domainClosureBlocker",
        "boundaryFluxCancellationBlocker",
        "quotientSelfAdjointnessBlocker",
        "h3aContinuumTransferBlocker",
    ):
        assert constructor in composite_text

    assert re.search(
        r"\bymaFiniteDominationArithmeticBlockerCountIs4\s*=\s*refl\b",
        composite_text,
    )
