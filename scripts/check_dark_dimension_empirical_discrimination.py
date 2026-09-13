from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionEmpiricalDiscriminationExact.agda": [
        "module DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact where",
        "bedroyaReportedFit",
        "darkAcousticOscillationComparator",
        "reportedFitDoesNotEqualHeldOutPrediction",
        "reportedPreferenceDoesNotUniquelyIdentifyDarkDimension",
        "alternativeMechanismKeepsModelIdentityOpen",
        "darkDimensionPredictionAdmissionStillNonPromoting",
        "externalPublishedFitDoesNotPayDASHIDerivedPrediction",
        "cPrimeBestFitFiveHundredths",
        "cPrimeUncertaintyOneHundredth",
        "cPrimeFifthForceUpperBoundTwoTenths",
        "10.1103/1rsq-cv2m",
        "10.1103/y31p-9g5k",
    ],
    "DASHI/Unified/DarkDimensionGRQuantumPromotionAdapterExact.agda": [
        "import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination",
        "phenomenologyDiscriminationDoesNotPayEmpiricalCompletion",
        "alternativeMechanismKeepsUnificationPromotionBlocked",
    ],
    "scripts/check_dark_dimension_string_promotion_boundary.py": [
        "DarkDimensionEmpiricalDiscriminationExact",
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

print("Dark-dimension empirical discrimination static contract: OK")
