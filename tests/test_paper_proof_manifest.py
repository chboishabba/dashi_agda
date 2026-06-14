from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from types import ModuleType

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
GENERATOR_PATH = REPO_ROOT / "scripts" / "generate_paper_proof_manifest.py"
CANONICAL_BASENAME = "core_papers_theorem_var_manifest"
COMPAT_BASENAME = "paper1_paper3_theorem_var_manifest"


@pytest.fixture(scope="module")
def manifest_module() -> ModuleType:
    spec = importlib.util.spec_from_file_location("generate_paper_proof_manifest", GENERATOR_PATH)
    assert spec is not None
    assert spec.loader is not None

    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture()
def generated_payloads(tmp_path: Path, manifest_module: ModuleType) -> dict[str, dict[str, object]]:
    manifest_module.write_outputs(manifest_module.ROWS, tmp_path)
    return {
        basename: json.loads((tmp_path / f"{basename}.json").read_text(encoding="utf-8"))
        for basename in (CANONICAL_BASENAME, COMPAT_BASENAME)
    }


def test_canonical_manifest_basename_and_row_count_include_paper8(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    payload = generated_payloads[CANONICAL_BASENAME]
    rows = payload["rows"]
    assert isinstance(rows, list)

    paper8_rows = [row for row in rows if row["paper"] == "Paper8 Unification"]
    assert payload["basename"] == CANONICAL_BASENAME
    assert payload["compatibility_alias"] is False
    assert payload["row_count"] == len(rows)
    assert paper8_rows
    assert payload["row_count"] == (len(rows) - len(paper8_rows)) + len(paper8_rows)


def test_compatibility_alias_manifest_is_marked_true(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    payload = generated_payloads[COMPAT_BASENAME]
    assert payload["basename"] == COMPAT_BASENAME
    assert payload["compatibility_alias"] is True


def test_expected_paper8_rows_exist(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    rows = generated_payloads[CANONICAL_BASENAME]["rows"]
    assert isinstance(rows, list)
    paper8_keys = {
        (row["lemma"], row["agda_file"], row["exact_var"], row["expected_status"])
        for row in rows
        if row["paper"] == "Paper8 Unification"
    }

    expected_rows = {
        (
            "Paper 8 core thesis receipt",
            "DASHI/Physics/Closure/Paper8CoreThesisReceipt.agda",
            "canonicalPaper8CoreThesisReceipt",
            "recorded",
        ),
        (
            "Paper 8 terminal promotion guard",
            "DASHI/Physics/Closure/Paper8CoreThesisReceipt.agda",
            "paper8CoreThesisKeepsTerminalFalse",
            "false",
        ),
        (
            "Millennium tower schema",
            "DASHI/Physics/Closure/MillenniumTowerSchemaReceipt.agda",
            "canonicalMillenniumTowerSchemaReceipt",
            "recorded",
        ),
        (
            "Millennium tower YM instance",
            "DASHI/Physics/Closure/MillenniumTowerYangMillsInstanceReceipt.agda",
            "canonicalMillenniumTowerYangMillsInstanceReceipt",
            "recorded",
        ),
        (
            "Millennium tower NS instance",
            "DASHI/Physics/Closure/MillenniumTowerNavierStokesInstanceReceipt.agda",
            "canonicalMillenniumTowerNavierStokesInstanceReceipt",
            "recorded",
        ),
        (
            "U-1a-H decomposition blocker",
            "DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda",
            "scaleInvariantCrossTermDecompositionProved",
            "false",
        ),
        (
            "Unification authority review no-promotion guard",
            "DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda",
            "TerminalPromotionFromUnificationAuthorityReviewPacket",
            "false",
        ),
        (
            "DCHoTT adapter terminal guard",
            "DASHI/DCHoTT/UnificationCandidate.agda",
            "dchottUnificationCandidateTerminalFalse",
            "false",
        ),
        (
            "Cubical adapter incompatibility surface",
            "DASHI/Cubical/UnificationCandidate.agda",
            "unificationCubicalAdapterIncompatibility",
            "adapter-boundary",
        ),
    }
    assert expected_rows <= paper8_keys
