from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionPredictionQuantityAdapterExact.agda": [
        "module DASHI.Empirical.DarkDimensionPredictionQuantityAdapterExact where",
        "predictionMetreUnit",
        "oneMicrometreAsPredictionQuantity",
        "thirtyMicrometresAsPredictionQuantity",
        "microRadiusLowerBridge",
        "microRadiusUpperBridge",
        "exactRationalMetreEncodingAvoidsExponentSignAmbiguity",
        "quantityBridgeDoesNotLockModelSeparation",
        "DASHI.Physics.Units.SI",
        "DASHI.Empirical.GRQuantumPredictionProtocol",
    ],
    "DASHI/Empirical/DarkDimensionQuantitativeEnvelopeExact.agda": [
        "import DASHI.Empirical.DarkDimensionPredictionQuantityAdapterExact as QuantityAdapter",
        "predictionQuantityAdapterAvailableButSeparationStillOpen",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_prediction_quantity_adapter.py",
        "DASHI/Empirical/DarkDimensionPredictionQuantityAdapterExact.agda",
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

print("Dark-dimension prediction quantity adapter static contract: OK")
