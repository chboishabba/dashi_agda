from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
MODULE = REPO_ROOT / "DASHI" / "Interop" / "FiberedCrankDASHISystem.agda"


@pytest.fixture(scope="module")
def module_text() -> str:
    return MODULE.read_text(encoding="utf-8")


def run_agda(path: Path) -> subprocess.CompletedProcess[str]:
    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    return subprocess.run(
        [agda, "-i", ".", str(path.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )


def bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n"
        rf"{re.escape(name)}\s*=\s*{expected}\b",
        text,
    ) is not None


def test_fibered_crank_dashi_system_typechecks_with_agda() -> None:
    result = run_agda(MODULE)
    assert result.returncode == 0, result.stdout + result.stderr


def test_core_record_and_vertical_preservation_surface(module_text: str) -> None:
    for required in (
        "record FiberedCrankDASHISystem",
        "Artifact",
        "Semantic",
        "projection",
        "Candidate",
        "generate",
        "Score",
        "Nat",
        "Witness",
        "Authority",
        "Invariant",
        "observe",
        "record VerticalTransformPreservation",
        "semanticPreserved",
        "scoreMonotone",
        "witnessPreserved",
        "invariantObservedAfterTransform",
    ):
        assert required in module_text, required


def test_jmd_terms_are_fail_closed_bridge_vocabulary(module_text: str) -> None:
    lowered = module_text.lower()

    for required in (
        "fail-closed",
        "imported jmd bridge vocabulary",
        "crank",
        "protagonist",
        "no jmd term is promoted",
        "bridgeVocabularyOnly",
        "importedJMDBridgeVocabulary",
        "jmdCrankBridgeVocabulary",
        "jmdProtagonistBridgeVocabulary",
    ):
        assert required.lower() in lowered, required

    for flag in (
        "jmdCrankTermPromotedToDASHIClaim",
        "jmdProtagonistTermPromotedToDASHIClaim",
        "fiberedCrankDASHIPromotesJMDTerms",
    ):
        assert bool_assignment(module_text, flag, False), flag
        assert f"{flag}IsFalse" in module_text


def test_concrete_finite_instance_is_inhabited_and_monotone(
    module_text: str,
) -> None:
    for required in (
        "data BitArtifact",
        "constantBitProjection",
        "BitVerticalTransform",
        "bitVerticalTransformPreservation",
        "concreteFiniteBoolLikeFiberedCrankDASHISystem",
        "concreteFiniteInstanceUsesConstantProjection",
        "concreteFiniteInstanceScoreMonotoneInhabited",
    ):
        assert required in module_text, required

    assert bool_assignment(
        module_text,
        "concreteFiniteInstanceUsesConstantProjection",
        True,
    )
    assert bool_assignment(
        module_text,
        "concreteFiniteInstanceScoreMonotoneInhabited",
        True,
    )
