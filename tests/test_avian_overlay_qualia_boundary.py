from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
BIOLOGY = REPO_ROOT / "DASHI" / "Biology"
INTEROP = REPO_ROOT / "DASHI" / "Interop"
REASONING = REPO_ROOT / "DASHI" / "Reasoning"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "avian_overlay_qualia_boundary_audit.py"

MODULES = {
    "DASHI.Biology.AvianVisualOverlayQuotient": {
        "path": BIOLOGY / "AvianVisualOverlayQuotient.agda",
        "identifiers": (
            "AvianVisualOverlayQuotient",
            "subjectiveQualiaRecovered",
            "subjectiveQualiaRecoveredIsFalse",
            "noDirectSubjectiveReportBoundary",
        ),
        "boundary_terms": (
            "observable",
            "quotient",
            "qualia",
            "false",
        ),
    },
    "DASHI.Biology.AvianRFOverlayManipulationReceipt": {
        "path": BIOLOGY / "AvianRFOverlayManipulationReceipt.agda",
        "identifiers": (
            "AvianRFOverlayManipulationReceipt",
            "oscillatingRFField",
            "RFManipulationRole",
            "rfNoEthicalPerturbationLicenseFlag",
        ),
        "boundary_terms": (
            "rf",
            "perturbation",
            "observable",
            "non",
            "promot",
        ),
    },
    "DASHI.Biology.AvianHardProblemResidual": {
        "path": BIOLOGY / "AvianHardProblemResidual.agda",
        "identifiers": (
            "AvianHardProblemResidual",
            "phenomenalContentGap",
            "phenomenalContentRecoveredIsFalse",
            "consciousnessClosureIsFalse",
        ),
        "boundary_terms": (
            "hard problem",
            "residual",
            "qualia",
            "false",
        ),
    },
    "DASHI.Interop.AvianCompassPNFSemanticBridge": {
        "path": INTEROP / "AvianCompassPNFSemanticBridge.agda",
        "identifiers": (
            "AvianCompassPNFSemanticBridge",
            "PredicatePNF",
            "pnfSemanticTruthAuthorityIsFalse",
            "qualiaPromotionIsFalse",
        ),
        "boundary_terms": (
            "pnf",
            "semantic",
            "bridge",
            "non",
            "promot",
        ),
    },
    "DASHI.Interop.SensibLawResidualLattice": {
        "path": INTEROP / "SensibLawResidualLattice.agda",
        "identifiers": (
            "SensibLawResidualLattice",
            "PredicatePNF",
            "PNFEmissionReceipt",
            "receiptResidual",
            "SensibLawResidualBridgeSurface",
        ),
        "boundary_terms": (
            "pnf",
            "residual",
            "runtime",
            "receipt",
            "not a parser",
        ),
    },
    "DASHI.Interop.QualiaTranscriptPNFSemanticBridge": {
        "path": INTEROP / "QualiaTranscriptPNFSemanticBridge.agda",
        "aggregate_import": False,
        "identifiers": (
            "QualiaTranscriptPNFSemanticBridge",
            "TranscriptReportQuotient",
            "transcriptReportQuotient",
            "transcriptPNF",
            "reportQuotientPromotedIsFalse",
            "RuntimeQualiaTranscriptPNFPayload",
            "RuntimeReceiptReportQuotient",
            "auditScriptOnly",
        ),
        "boundary_terms": (
            "transcript",
            "pnf",
            "quotient",
            "qualia",
            "runtime",
            "false",
        ),
    },
    "DASHI.Biology.ObserverPerceptualManifoldResidual": {
        "path": BIOLOGY / "ObserverPerceptualManifoldResidual.agda",
        "aggregate_import": False,
        "identifiers": (
            "ObserverPerceptualManifoldResidual",
            "MultiSpeakerResidual",
            "multiSpeakerResidual",
            "multiSpeakerResidualsPromotedIsFalse",
            "perceptualManifoldProjectionDefect",
            "projectionDefectPromotedIsFalse",
            "BlockedPhenomenalClosure",
            "blockedPhenomenalClosure",
            "blockedPhenomenalClosureIsFalse",
            "ObserverState",
            "StateSpecificObserverQuotient",
            "StateShiftProjectionDefect",
            "stateModifiedFibresNonempty",
            "stateShiftPhenomenalRecoveryIsFalse",
        ),
        "boundary_terms": (
            "observer",
            "manifold",
            "residual",
            "projection defect",
            "phenomenal",
            "state",
            "false",
        ),
    },
    "DASHI.Reasoning.MultiObserverScienceQuotientQualiaBridge": {
        "path": REASONING / "MultiObserverScienceQuotientQualiaBridge.agda",
        "identifiers": (
            "MultiObserverQuotientFusion",
            "observerChannelsNonempty",
            "partialReconstructionPromotedIsTrue",
            "projectionDefectBoundedIsTrue",
            "inhabitedExperienceRecoveredIsFalse",
        ),
        "boundary_terms": (
            "multi",
            "observer",
            "quotient",
            "fusion",
            "false",
        ),
    },
    "DASHI.Biology.AvianMagnetoreceptionExtraFibreBoundary": {
        "path": BIOLOGY / "AvianMagnetoreceptionExtraFibreBoundary.agda",
        "identifiers": (
            "AvianMagnetoreceptionExtraFibreBoundary",
            "perceptualQuotientGeometryExperimentallyConstrained",
            "qualiaGeometryClaimIsFalse",
        ),
        "boundary_terms": (
            "avian",
            "magnetoreception",
            "extra",
            "fibre",
            "false",
        ),
    },
}

OBSERVER_QUOTIENT_COMPLETION_TOKENS = (
    "StateSpecificObserverQuotient",
    "StateShiftProjectionDefect",
    "RuntimeQualiaTranscriptPNFPayload",
    "RuntimeReceiptReportQuotient",
    "auditScriptOnly",
    "MultiObserverQuotientFusion",
    "AvianMagnetoreceptionExtraFibreBoundary",
    "perceptualQuotientGeometryExperimentallyConstrained",
    "qualiaGeometryClaimIsFalse",
)


@pytest.fixture(scope="module")
def module_texts() -> dict[str, str]:
    texts: dict[str, str] = {}
    for module_name, spec in MODULES.items():
        path = spec["path"]
        assert path.is_file(), f"missing expected Agda module for {module_name}: {path}"
        texts[module_name] = path.read_text(encoding="utf-8")
    return texts


def test_avian_overlay_modules_exist_and_are_not_postulated(
    module_texts: dict[str, str],
) -> None:
    for module_name, text in module_texts.items():
        assert f"module {module_name} where" in text
        assert "postulate" not in text.lower(), module_name


def test_avian_overlay_modules_record_required_identifiers(
    module_texts: dict[str, str],
) -> None:
    for module_name, spec in MODULES.items():
        text = module_texts[module_name]
        for identifier in spec["identifiers"]:
            assert identifier in text, f"{module_name} missing {identifier}"


def test_observer_quotient_completion_surfaces_record_new_tokens(
    module_texts: dict[str, str],
) -> None:
    combined = "\n".join(module_texts.values())
    for token in OBSERVER_QUOTIENT_COMPLETION_TOKENS:
        assert token in combined, f"observer quotient completion token missing: {token}"

    transcript_text = module_texts["DASHI.Interop.QualiaTranscriptPNFSemanticBridge"]
    assert "auditScriptOnly" in transcript_text
    assert "RuntimeQualiaTranscriptPNFPayload" in transcript_text
    assert "RuntimeReceiptReportQuotient" in transcript_text

    fusion_text = module_texts["DASHI.Reasoning.MultiObserverScienceQuotientQualiaBridge"]
    assert "MultiObserverQuotientFusion" in fusion_text
    assert "partialReconstructionPromotedIsTrue" in fusion_text
    assert "projectionDefectBoundedIsTrue" in fusion_text

    avian_text = module_texts["DASHI.Biology.AvianMagnetoreceptionExtraFibreBoundary"]
    assert "perceptualQuotientGeometryExperimentallyConstrained" in avian_text
    assert "qualiaGeometryClaimIsFalse" in avian_text


def test_avian_overlay_modules_record_false_boundary_language(
    module_texts: dict[str, str],
) -> None:
    combined = "\n".join(module_texts.values()).lower()
    assert "true" in combined
    assert "false" in combined
    assert "subjective" in combined
    assert "qualia" in combined
    assert "hard problem" in combined
    assert "non" in combined and "promot" in combined

    for module_name, spec in MODULES.items():
        lowered = module_texts[module_name].lower()
        for term in spec["boundary_terms"]:
            assert term in lowered, f"{module_name} missing boundary term {term!r}"


def _audit_check_rows(payload: object) -> list[dict[str, object]]:
    if not isinstance(payload, dict):
        return []

    checks = payload.get("checks")
    if isinstance(checks, list):
        return [row for row in checks if isinstance(row, dict)]
    if isinstance(checks, dict):
        rows: list[dict[str, object]] = []
        for name, value in checks.items():
            if isinstance(value, dict):
                row = {"name": name}
                row.update(value)
                rows.append(row)
            else:
                rows.append({"name": name, "passed": value})
        return rows

    required = payload.get("required_checks")
    if isinstance(required, dict):
        return [{"name": name, "passed": value} for name, value in required.items()]
    return []


def _row_passed(row: dict[str, object]) -> bool | None:
    for key in ("passed", "pass", "ok", "status"):
        value = row.get(key)
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            lowered = value.lower()
            if lowered in {"pass", "passed", "ok", "true"}:
                return True
            if lowered in {"fail", "failed", "false"}:
                return False
            if lowered in {"pending", "skip", "skipped"}:
                return None
    return None


def test_optional_avian_overlay_audit_json_passes_non_aggregate_checks() -> None:
    if not AUDIT_SCRIPT.is_file():
        pytest.skip("avian overlay qualia boundary audit script is not present yet")

    result = subprocess.run(
        [
            "python",
            str(AUDIT_SCRIPT.relative_to(REPO_ROOT)),
            "--allow-missing-aggregate",
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    payload = json.loads(result.stdout)
    encoded = json.dumps(payload)
    for module_name, spec in MODULES.items():
        if spec.get("audit_json", True) is False:
            continue
        assert module_name.rsplit(".", maxsplit=1)[-1] in encoded
    for token in OBSERVER_QUOTIENT_COMPLETION_TOKENS:
        assert token in encoded

    rows = _audit_check_rows(payload)
    assert rows, "audit JSON did not expose check rows"
    for row in rows:
        name = str(row.get("name", "")).lower()
        if "aggregate" in name:
            continue
        assert _row_passed(row) is True, row


def test_avian_overlay_modules_imported_by_everything_when_integrated() -> None:
    text = EVERYTHING.read_text(encoding="utf-8")
    missing = [
        module_name
        for module_name, spec in MODULES.items()
        if spec.get("aggregate_import", True) and f"import {module_name}" not in text
    ]
    assert not missing
