from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionModelObservableMatrixExact.agda": [
        "module DASHI.Empirical.DarkDimensionModelObservableMatrixExact where",
        "ModelKind",
        "ObservableKind",
        "darkDimensionCPrimeCell",
        "darkDimensionRadiusCell",
        "darkDimensionDAOAmplitudeCell",
        "daoAmplitudeCell",
        "daoCPrimeCell",
        "daoRadiusCell",
        "crossCoordinateDifferenceIsWrongType",
        "sharedObservableNumericalSeparationStillOpen",
        "sameObservableRequirement",
        "DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact",
    ],
    "DASHI/Empirical/DarkDimensionQuantitativeEnvelopeExact.agda": [
        "import DASHI.Empirical.DarkDimensionModelObservableMatrixExact",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_model_observable_matrix.py",
        "DASHI/Empirical/DarkDimensionModelObservableMatrixExact.agda",
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

print("Dark-dimension model-observable matrix static contract: OK")
