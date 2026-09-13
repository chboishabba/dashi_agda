from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionSharedBAOObservableExact.agda": [
        "module DASHI.Empirical.DarkDimensionSharedBAOObservableExact where",
        "SharedBAOObservable",
        "transverseDMOverRd",
        "radialDHOverRd",
        "darkDimensionTransverseProjection",
        "darkDimensionRadialProjection",
        "daoTransverseProjection",
        "daoRadialProjection",
        "sharedObservableIdentityPaid",
        "sharedObservableNumericalPredictionsStillOpen",
        "sameObservableDoesNotMeanSameMechanism",
        "sharedObservableDoesNotPayQuantitativePrediction",
        "10.1103/1rsq-cv2m",
        "10.1103/y31p-9g5k",
    ],
    "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda": [
        "module DASHI.Empirical.DarkDimensionSharedBAOProspectiveWeldExact where",
        "open import Agda.Builtin.Bool using (false; true)",
        "sharedBAOIdentityPaidButNumericalSeparationOpen",
        "sharedBAOStillDoesNotLockProspectivePacket",
        "DarkDimensionSharedBAOObservableExact",
        "DarkDimensionProspectiveDiscriminatorExact",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_shared_bao_observable.py",
        "DASHI/Empirical/DarkDimensionSharedBAOObservableExact.agda",
        "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda",
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

print("Dark-dimension shared BAO observable static contract: OK")
