from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "module DASHI.Empirical.DarkDimensionSameKeyPredictionDebtExact where",
        "SameKeyPredictionDerivationDebt",
        "daoExecutableModelLocated",
        "darkDimensionExecutableModelLocated",
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
        "sameKeyPredictionDerivationDebtStillBlocksProspectiveSeparation",
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
