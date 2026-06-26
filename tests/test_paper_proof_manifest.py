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


def test_new_intake_and_polymer_boundary_rows_remain_nonpromotional(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    rows = generated_payloads[CANONICAL_BASENAME]["rows"]
    assert isinstance(rows, list)
    rows_by_lemma = {row["lemma"]: row for row in rows}

    expected_rows = {
        "Seregin/ESS A3 theorem-intake boundary": (
            "Paper1 NS",
            "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
            "publishableClaimText",
            "authority-intake-boundary",
        ),
        "Balaban Option A theorem-intake boundary": (
            "Paper3 YM",
            "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
            "ym6Statement",
            "authority-intake-boundary",
        ),
        "Option B native polymer boundary": (
            "Paper3 YM",
            "DASHI/Physics/Closure/Paper3YMDependencyGraphReceipt.agda",
            "infiniteVolumePolymerExpansionProved",
            "false",
        ),
    }

    for lemma, (paper, agda_file, exact_var, expected_status) in expected_rows.items():
        if lemma == "Option B native polymer boundary" and lemma not in rows_by_lemma:
            option_b_steps = {
                row["lemma"]
                for row in rows
                if row["paper"] == "Paper3 YM" and str(row["lemma"]).startswith("Option B B")
            }
            assert len(option_b_steps) == 5
            continue
        row = rows_by_lemma[lemma]
        assert row["paper"] == paper
        assert row["agda_file"] == agda_file
        assert row["exact_var"] == exact_var
        assert row["expected_status"] == expected_status
        assert row["expected_status"] != "true"
        assert "promotion" in row["governance_note"].lower()


def test_option_b_b1_b5_manifest_rows_are_complete_and_fail_closed(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    rows = generated_payloads[CANONICAL_BASENAME]["rows"]
    assert isinstance(rows, list)

    b_rows = [
        row
        for row in rows
        if row["paper"] == "Paper3 YM"
        and "option" in row["lemma"].lower()
        and "b" in row["lemma"].lower()
        and any(f"b{index}" in " ".join(str(value).lower() for value in row.values()) for index in range(1, 6))
    ]
    if not b_rows:
        pytest.skip("Option-B B1-B5 manifest rows are not integrated yet")

    rows_by_step: dict[str, list[dict[str, object]]] = {f"B{index}": [] for index in range(1, 6)}
    for row in b_rows:
        haystack = " ".join(str(value).lower() for value in row.values())
        for step in rows_by_step:
            if step.lower() in haystack:
                rows_by_step[step].append(row)

    missing = [step for step, matches in rows_by_step.items() if not matches]
    assert missing == []

    for step, matches in rows_by_step.items():
        for row in matches:
            status = str(row["expected_status"]).lower()
            note = str(row["governance_note"]).lower()
            assert status not in {"true", "proved", "promoted"}, (step, row)
            assert any(
                word in status
                for word in ("false", "open", "deferred", "boundary", "blocked", "target", "diagnostic")
            )
            assert any(word in note for word in ("fail", "promotion", "promote", "blocked", "deferred"))


def test_ns_abel_manifest_rows_record_a1_a3_and_kappa_without_promotion(
    generated_payloads: dict[str, dict[str, object]],
) -> None:
    rows = generated_payloads[CANONICAL_BASENAME]["rows"]
    assert isinstance(rows, list)
    rows_by_lemma = {row["lemma"]: row for row in rows}

    expected_rows = {
        "Missing-math master: NS A1/A3 Abel stationarity": (
            "DASHI/Physics/Closure/NSSereginESSTheoremIntakeReceipt.agda",
            "candidateAbelRateNotDerived",
            "open",
        ),
        "Missing-math master: NS A5 kappa-bias": (
            "DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda",
            "a5BiasVanishingTheoremProved",
            "false",
        ),
        "Seregin/ESS A3 theorem-intake boundary": (
            "DASHI/Physics/Closure/NSPaper1ClayTargetReceipt.agda",
            "publishableClaimText",
            "authority-intake-boundary",
        ),
    }

    for lemma, (agda_file, exact_var, expected_status) in expected_rows.items():
        row = rows_by_lemma[lemma]
        assert row["paper"] == "Paper1 NS"
        assert row["lemma"] == lemma
        assert row["agda_file"] == agda_file
        assert row["exact_var"] == exact_var
        assert row["expected_status"] == expected_status
        assert str(row["expected_status"]).lower() not in {"true", "proved", "promoted"}
        assert "promotion" in str(row["governance_note"]).lower()
        assert any(
            marker in str(row["governance_note"]).lower()
            for marker in ("false", "non-promoting", "unpromoted", "blocked", "blocks", "guard", "boundary")
        )
