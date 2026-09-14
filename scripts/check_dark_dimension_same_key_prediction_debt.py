from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "module DASHI.Empirical.DarkDimensionSameKeyPredictionDebtExact where",
        "import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun",
        "import DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact as BedroyaAcquisition",
        "SameKeyPredictionDerivationDebt",
        "daoExecutableModelLocated",
        "darkDimensionExecutableModelLocated",
        "daoExecutableRevisionPinned",
        "daoExecutionConfigSurfaceLocated",
        "daoExecutedByDASHI",
        "daoExecutableRevisionPinPaid",
        "daoExecutionConfigSurfacePaid",
        "daoExecutionStillNotRun",
        "daoReconstructionRuntimeRequestLocated",
        "daoReconstructionRuntimeReceiptStillOpen",
        "daoReconstructionVectorStillOpen",
        "darkDimensionExecutableStillOpen",
        "bedroyaSameObjectAcquisitionStillOpen",
        "BedroyaAcquisition.childSameObjectStillUnacquired",
        "bedroyaPostIdentitySupportStageDefined",
        "BedroyaAcquisition.postIdentitySupportStillRequiresSourcePayment",
        "lrg1TransversePredictionRequest", "lrg1RadialPredictionRequest",
        "lrg2TransversePredictionRequest", "lrg2RadialPredictionRequest",
        "lrg3Elg1TransversePredictionRequest", "lrg3Elg1RadialPredictionRequest",
        "elg2TransversePredictionRequest", "elg2RadialPredictionRequest",
        "qsoTransversePredictionRequest", "qsoRadialPredictionRequest",
        "lyaTransversePredictionRequest", "lyaRadialPredictionRequest",
        "daoDRMDClassRevision",
        "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9",
        "input/DRMD.ini",
        "rs_drag",
        "rs_d_drmd",
        "daoSameKeyBAOVectorDerived",
        "darkDimensionSameKeyBAOVectorDerived",
        "largeScaleStructureIndependentDoesNotMeanChronologicallyHeldOut",
        "sameKeyPredictionDebtStillOpen",
        "sharedBAONumericalSeparationStillBlocked",
        "DRMD-CLASS",
        "2602.23895",
        "2507.03090",
    ],
    "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda": [
        "import DASHI.Empirical.DarkDimensionSameKeyPredictionDebtExact as PredictionDebt",
        "sameKeyPredictionDebtStatusStillOpenForProspectiveSeparation",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_same_key_prediction_debt.py",
        "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda",
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

print("Dark-dimension same-key prediction debt static contract: OK")
