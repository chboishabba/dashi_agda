from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionCrossDomainEvidenceWeldExact.agda": [
        "module DASHI.Empirical.DarkDimensionCrossDomainEvidenceWeldExact where",
        "import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence",
        "import DASHI.Core.IntersectionalNonFactorability as NonFactor",
        "import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as AcquisitionAssessment",
        "import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction",
        "import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as BedroyaManifest",
        "import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun",
        "CurrentSearchResult",
        "searchedButNotLocated",
        "notLocatedDoesNotBecomeAbsent",
        "acquisitionNoMatchDoesNotBecomeAbsence",
        "bedroyaChainSearchDiligence",
        "MarginalSummaryState",
        "sameMarginalsDifferentSixKeyWitness",
        "marginalsCannotFactorToUniqueSixKeyVector",
        "equationsAndMarginalsCannotAutoDetermineSixKeyVector",
        "daoRuntimeArtifactStillReconstructionOnly",
        "reconstructionReceiptDoesNotBecomeHeldOutPrediction",
        "quantitativePredictionBoundaryStillOpen",
        "sourceNonLocationStillOpen",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionCrossDomainEvidenceWeldExact as CrossDomain",
        "crossDomainEvidenceWeldStillBlocksPromotion",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_cross_domain_evidence_weld.py",
        "DASHI/Empirical/DarkDimensionCrossDomainEvidenceWeldExact.agda",
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Dark-dimension cross-domain evidence weld static contract: OK")
