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
    / "ScaleLocalObservableCriterion.agda"
)


def run_agda(path: Path) -> None:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.fixture(scope="module")
def module_text() -> str:
    assert MODULE.is_file(), "missing ScaleLocalObservableCriterion Agda module"
    return MODULE.read_text(encoding="utf-8")


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def test_scale_local_observable_criterion_typechecks(module_text: str) -> None:
    assert module_text
    run_agda(MODULE)


def test_finite_depth_projection_and_fiber_equivalence_surface(module_text: str) -> None:
    for term in (
        "data Artifact",
        "atomA",
        "atomB",
        "atomC",
        "atomD",
        "data Depth",
        "depth0",
        "depth1",
        "depth2",
        "project : Depth → Artifact → ProjectedArtifact",
        "FiberEquivalent",
        "project d x ≡ project d y",
        "ClopenFiber",
    ):
        assert term in module_text, term


def test_observable_factorization_iff_and_canonical_witnesses(module_text: str) -> None:
    for term in (
        "FactorsThroughProjection",
        "ConstantOnFibers",
        "factor-through⇒constant-on-fibers",
        "constant-on-fibers⇒factor-through",
        "ObservableFactorsIffConstantOnFibers",
        "finiteToyObservableCriterion",
        "canonicalObservable",
        "canonicalFactorsThroughProjection",
        "canonicalConstantOnFibers",
        "canonicalForwardDirectionInhabited",
        "canonicalBackwardDirectionInhabited",
        "canonicalClopenFiber",
    ):
        assert term in module_text, term


def test_promotion_flags_are_fail_closed(module_text: str) -> None:
    assert agda_bool_assignment(
        module_text, "scaleLocalCriterionClosedForFiniteToy", True
    )
    for name in (
        "continuumObservablePromoted",
        "physicsLawPromoted",
        "clayPromotion",
    ):
        assert agda_bool_assignment(module_text, name, False), name

    forbidden_true = re.findall(
        r"\b(continuumObservablePromoted|physicsLawPromoted|clayPromotion)\s*=\s*true\b",
        module_text,
    )
    assert forbidden_true == []
