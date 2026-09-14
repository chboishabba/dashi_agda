from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaBAOReadinessExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaBAOReadinessExact where",
        "import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin",
        "import DASHI.Core.IntersectionalNonFactorability as NonFactor",
        "import DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact as Input",
        "import DASHI.Empirical.DarkDimensionBedroyaConditionalRuntimeExact as Runtime",
        "BAOReadinessState",
        "nothingPaid",
        "backgroundOnlyPaid",
        "rDragOnlyPaid",
        "backgroundAndRDragPaid",
        "backgroundReadinessAxis",
        "rDragReadinessAxis",
        "sameKeyBAOReadinessJoin",
        "backgroundOnlyCannotRecoverRDrag",
        "rDragOnlyCannotRecoverBackground",
        "bothAxesRequiredForSameKeyBAO",
        "backgroundInputStillOpen",
        "rDragStillOpen",
        "runtimeSchemaDoesNotManufactureEitherAxis",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionBedroyaBAOReadinessExact as BedroyaBAOReadiness",
        "bedroyaTwoStageBAOReadinessStillOpen",
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

print("Dark-dimension Bedroya BAO readiness static contract: OK")
