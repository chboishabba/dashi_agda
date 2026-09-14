from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaConditionalRuntimeExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaConditionalRuntimeExact where",
        "import DASHI.Core.ProofDebtRouterExact as ProofDebt",
        "import DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact as Input",
        "import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey",
        "CompleteBedroyaBackgroundInput",
        "h0Input",
        "omegaR0Input",
        "omegaB0Input",
        "sampledDMNormalizationInput",
        "v0NormalizationInput",
        "initialScalarVelocityInput",
        "sameFitRDragInput",
        "inputProvenanceReference",
        "BedroyaBackgroundVectorRequest",
        "sixObservationRedshiftsPinned",
        "BedroyaBackgroundVectorReceipt",
        "hVectorPresent",
        "dmVectorPresent",
        "dhVectorPresent",
        "baoRatiosPresent",
        "runBedroyaBackgroundConditionally",
        "ProofDebt.ConditionalDevelopment",
        "NoCompleteInputMeansNoRuntimeReceipt",
        "noCompleteInputDoesNotManufactureRuntimeReceipt",
        "BackgroundReceiptWithoutRDragPaysBAORatios",
        "backgroundReceiptDoesNotPayBAOWithoutRDrag",
        "canonicalRuntimeRequestStillBlocked",
        "Input.completeBackgroundInputStillOpen",
        "Input.exactRDragSameFitStillOpen",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionBedroyaConditionalRuntimeExact as BedroyaRuntime",
        "bedroyaConditionalRuntimeStillBlocked",
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

print("Dark-dimension Bedroya conditional runtime static contract: OK")
