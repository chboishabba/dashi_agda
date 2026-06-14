from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DASHI_ROOT = REPO_ROOT / "DASHI"
EVERYTHING = DASHI_ROOT / "Everything.agda"


EXPECTED_MODULES = {
    "DASHI.Promotion.SIExactConstantParsedCarrierRequest": {
        "path": "DASHI/Promotion/SIExactConstantParsedCarrierRequest.agda",
        "required": (
            "canonicalDeltaNuCsNaturalCarrier",
            "canonicalCMetrePerSecondIntegerCarrier",
            "canonicalHScientificDecimalCarrier",
            "canonicalSIExactConstantParsedCarrierRequestManifest",
            "canonicalHCarrierDoesNotUseFloat",
        ),
        "false_guards": (
            "authorityArtifactPresent",
            "acceptedAuthorityTokenPresent",
            "consumerIngestionReceiptPresent",
            "anyNumericValuePromoted",
            "externalArtifactAccepted",
        ),
    },
    "DASHI.Promotion.SIDefiningConstantAuthorityEvidenceChecklist": {
        "path": "DASHI/Promotion/SIDefiningConstantAuthorityEvidenceChecklist.agda",
        "required": (
            "SIConstantAuthorityEvidenceChecklistManifest",
            "canonicalDeltaNuCsAuthorityEvidenceRow",
            "canonicalCAuthorityEvidenceRow",
            "canonicalHAuthorityEvidenceRow",
            "canonicalSIConstantAuthorityEvidenceChecklistManifest",
        ),
        "false_guards": (
            "anyArtifactEvidenceAccepted",
            "candidate256AuthorityTokenConstructed",
            "anyConsumerIngestionReceiptAccepted",
            "allParsedCarrierPayloadsAccepted",
            "anySIConstantPromoted",
        ),
    },
    "DASHI.Promotion.SIExactConstantConsumerIngestionBridge": {
        "path": "DASHI/Promotion/SIExactConstantConsumerIngestionBridge.agda",
        "required": (
            "SIExactConstantConsumerIngestionBridge",
            "canonicalDeltaNuCsConsumerIngestionBridgeRow",
            "canonicalCConsumerIngestionBridgeRow",
            "canonicalHConsumerIngestionBridgeRow",
            "canonicalSIExactConstantConsumerIngestionBridge",
        ),
        "false_guards": (
            "consumerIngestionReceiptPresent",
            "downstreamPromotionEnabled",
            "anyConsumerIngestionReceiptPresent",
            "anyNumericValuePromoted",
            "anyDownstreamPromotionEnabled",
        ),
    },
    "DASHI.Physics.Closure.AtomicClockSecondRealTimeTopologyRequest": {
        "path": "DASHI/Physics/Closure/AtomicClockSecondRealTimeTopologyRequest.agda",
        "required": (
            "SISecondToRealLineMetricTopologyParameter",
            "StoneStrongContinuityLawFields",
            "RealTimeOneParameterGroupLawFields",
            "canonicalAtomicClockSecondRealTimeTopologyRequest",
            "canonicalRequestPromotionAllowedFalse",
        ),
        "false_guards": (
            "realCarrierGuard",
            "metricTopologyGuard",
            "strongContinuityGuard",
            "physicalStonePromotionGuard",
            "promotionAllowed",
        ),
    },
    "DASHI.Physics.Closure.StoneHbarDimensionlessActionBridge": {
        "path": "DASHI/Physics/Closure/StoneHbarDimensionlessActionBridge.agda",
        "required": (
            "stoneExponentDimensionless",
            "canonicalStoneHbarActionDimensionCancellationReceipt",
            "canonicalOneParameterUnitaryGroupObligationReceipt",
            "canonicalStoneHbarDimensionlessActionBridge",
            "canonicalBridgeKeepsPhysicalSchrodingerPromotionFalse",
        ),
        "false_guards": (
            "physicalRealGroupLawSupplied",
            "physicalUnitaryGroupConstructed",
            "realCarrierSupplied",
            "hbarAuthorityPayloadSupplied",
            "physicalPromotionAllowed",
        ),
    },
    "DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw": {
        "path": "DASHI/Physics/Closure/QuantumClockDimensionlessObservableLaw.agda",
        "required": (
            "phaseProductDimensionless",
            "redshiftRatioDimensionless",
            "canonicalQuantumClockDimensionlessObservableLaw",
            "canonicalDimensionlessLawNoNumericPayloadClaim",
            "canonicalDimensionlessLawNoEmpiricalPromotionClaim",
        ),
        "false_guards": (
            "numericPayloadClaimed",
            "empiricalReceiptClaimed",
            "numericPredictionClaimed",
            "empiricalPromotionClaimed",
        ),
    },
    "DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest": {
        "path": "DASHI/Physics/Closure/QuantumClockEmpiricalRedshiftReceiptRequest.agda",
        "required": (
            "QuantumClockEmpiricalRedshiftReceiptRequest",
            "canonicalRequiredEvidenceRows",
            "poundRebkaRequested",
            "gpsClockComparisonRequested",
            "canonicalQuantumClockEmpiricalRedshiftReceiptRequest",
        ),
        "false_guards": (
            "empiricalReceiptAccepted",
            "evidenceAccepted",
            "ingestionReceiptPresent",
            "empiricalPromotionAllowed",
            "empiricalPromotionClaimed",
        ),
    },
    "DASHI.Promotion.SIMetreFromSecondAndCAdapter": {
        "path": "DASHI/Promotion/SIMetreFromSecondAndCAdapter.agda",
        "required": (
            "speedOfLightExactInteger",
            "canonicalExactSpeedOfLightDependency",
            "canonicalMetreFromSecondAndCNarrative",
            "canonicalRydbergWavenumberDimensionAdapter",
            "canonicalSIMetreFromSecondAndCAdapter",
        ),
        "false_guards": (
            "cArtifactLoaded",
            "cArtifactAccepted",
            "cRowPromoted",
            "authorityPayloadPromoted",
            "spectroscopyPromoted",
        ),
    },
    "DASHI.Promotion.RydbergSpectroscopyAuthorityPayloadRequest": {
        "path": "DASHI/Promotion/RydbergSpectroscopyAuthorityPayloadRequest.agda",
        "required": (
            "RydbergSpectroscopyAuthorityPayloadRequest",
            "canonicalRInfinityCODATAPayloadRequest",
            "electronMassReducedMassDependency",
            "protonMassReducedMassDependency",
            "canonicalRydbergSpectroscopyAuthorityPayloadRequestManifest",
        ),
        "false_guards": (
            "authorityPayloadAccepted",
            "parsedNumericCarrierAccepted",
            "nistASDTokenAccepted",
            "spectroscopyPromotionAllowed",
            "spectroscopyPromoted",
        ),
    },
    "DASHI.Physics.Closure.W4AtomicClockCandidateReceiptChecklist": {
        "path": "DASHI/Physics/Closure/W4AtomicClockCandidateReceiptChecklist.agda",
        "required": (
            "AtomicClockCandidateReceiptChecklistRow",
            "canonicalAtomicClockCandidateReceiptChecklistRows",
            "canonicalAtomicClockCandidateReceiptNoPromotionSummary",
            "canonicalAtomicClockCandidateReceiptChecklist",
            "canonicalAtomicClockCandidateChecklistTerminalGuard",
        ),
        "false_guards": (
            "authorityTokenConstructed",
            "externalAuthorityConstructed",
            "externalReceiptConstructed",
            "w4PhysicalCalibrationPromoted",
            "siAuthorityRowsPromoted",
        ),
    },
    "DASHI.Promotion.SIMetrologyPayloadDependencyDAG": {
        "path": "DASHI/Promotion/SIMetrologyPayloadDependencyDAG.agda",
        "required": (
            "SIMetrologyPayloadDependencyDAG",
            "canonicalSIMetrologyDAGNodes",
            "canonicalSIMetrologyDAGEdges",
            "canonicalSIMetrologyClosureOrder",
            "canonicalSIMetrologyPayloadDependencyDAG",
        ),
        "false_guards": (
            "promoted",
            "edgeCurrentlyClosed",
            "rowClosed",
            "guardValue",
            "terminalPromotionAllowed",
        ),
    },
}

FORBIDDEN_PROMOTION_PATTERNS = (
    r"\b\w*(?:Promoted|PromotionClaimed|ClaimPromoted|AuthorityAccepted|ArtifactAccepted)"
    r"\w*\s*=\s*true\b",
    r"\bconstructs(?:External|Candidate256|SISecond|Metrology)\w*\s*=\s*true\b",
    r"\blocal(?:External|Candidate256|SISecond|Metrology)\w*Constructed\s*=\s*true\b",
    r"\baccepted(?:External|Authority|Artifact|Calibration)\w*Present\s*=\s*true\b",
)


def read_text(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8", errors="replace")


def assignment_to_value(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    patterns = (
        rf"\b{re.escape(name)}\s*:\s*Bool\s*\n\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf";\s*{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}\s*=\s*{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*Is{'True' if value else 'False'}\s*:"
        rf"[\s\S]{{0,360}}\b{expected}\b",
        rf"\b{re.escape(name)}[A-Za-z0-9_']*\s*:[\s\S]{{0,360}}\b{expected}\b",
    )
    return any(re.search(pattern, text) for pattern in patterns)


def assert_any_false_guard(text: str, names: tuple[str, ...], label: str) -> None:
    assert any(assignment_to_value(text, name, False) for name in names), (
        f"{label} missing fail-closed false guard; expected one of: "
        + ", ".join(names)
    )
    promoted = [
        name
        for name in names
        if re.search(
            rf"(?:;\s*)?\b{re.escape(name)}\s*=\s*true\b",
            text,
        )
    ]
    assert promoted == [], f"{label} unexpectedly flips a guard true: {promoted}"


def module_texts() -> dict[str, str]:
    return {
        module: read_text(REPO_ROOT / spec["path"])
        for module, spec in EXPECTED_MODULES.items()
    }


def test_round_three_si_metrology_modules_exist_and_name_expected_surfaces() -> None:
    for module, spec in EXPECTED_MODULES.items():
        path = REPO_ROOT / spec["path"]
        text = read_text(path)
        assert f"module {module} where" in text
        missing = [name for name in spec["required"] if name not in text]
        assert missing == [], f"{module} missing expected names: {missing}"


def test_round_three_si_metrology_contact_strings_and_structural_values() -> None:
    combined = "\n".join(module_texts().values())

    for exact in (
        "9 192 631 770",
        "9192631770",
        "299792458",
        "6.62607015e-34",
        "Delta nu Cs",
        "BIPM",
        "NIST",
        "CODATA",
        "Pound-Rebka",
        "Gravity Probe A",
        "Candidate256",
        "Real carrier",
        "H * t / hbar",
        "dim(omega0 * Delta tau) = dimensionless",
        "dim(Delta U / c^2) = dimensionless",
        "metre = c * second / 299792458",
        "R_infinity",
        "NIST ASD",
    ):
        assert exact in combined, f"missing round-3 SI/metrology contact string: {exact}"


def test_round_three_si_metrology_fail_closed_booleans_remain_false() -> None:
    for module, spec in EXPECTED_MODULES.items():
        text = read_text(REPO_ROOT / spec["path"])
        assert_any_false_guard(text, spec["false_guards"], module)

        for pattern in FORBIDDEN_PROMOTION_PATTERNS:
            assert not re.search(pattern, text), (
                f"{module} contains forbidden promotion pattern: {pattern}"
            )


def test_round_three_si_metrology_modules_are_imported_by_everything_once() -> None:
    everything = read_text(EVERYTHING)

    for module in EXPECTED_MODULES:
        imports = re.findall(
            r"^\s*import\s+" + re.escape(module) + r"\s*$",
            everything,
            flags=re.MULTILINE,
        )
        assert imports == [f"import {module}"], (
            f"DASHI/Everything.agda must import exactly once: {module}"
        )
