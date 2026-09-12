from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Physics/Closure/DarkDimensionStringPromotionBoundaryExact.agda": [
        "module DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact where",
        "darkDimensionModelTestable",
        "micronScaleIsConditionalOnSwamplandPremises",
        "modelTestabilityDoesNotPromoteStringTheory",
        "positiveSignalDoesNotUniquelyIdentifyStringTheory",
        "modelNullDoesNotFalsifyStringTheorySimpliciter",
        "evolvingDarkEnergyDoesNotUniquelyIdentifySwampland",
        "theoryOfEverythingPromotionStillBlocked",
        "10.1007/JHEP02(2023)022",
        "10.1007/JHEP11(2023)109",
        "10.1103/PhysRevD.109.063540",
        "10.3847/2515-5172/ae8906",
        "10.1103/1rsq-cv2m",
    ],
    "DASHI/Empirical/DarkDimensionEmpiricalDiscriminationExact.agda": [
        "module DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact where",
        "bedroyaReportedFit",
        "darkAcousticOscillationComparator",
        "reportedFitDoesNotEqualHeldOutPrediction",
        "reportedPreferenceDoesNotUniquelyIdentifyDarkDimension",
        "alternativeMechanismKeepsModelIdentityOpen",
        "DarkDimensionEmpiricalDiscriminationExact",
        "10.1103/y31p-9g5k",
    ],
    "DASHI/Physics/Closure/GeneralGRCosmologyQuantumGravityRegression.agda": [
        "import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension",
        "darkDimensionTestableRegression",
        "darkDimensionStringPromotionBlockedRegression",
        "darkDimensionToEBlockedRegression",
    ],
    "DASHI/Unified/DarkDimensionGRQuantumPromotionAdapterExact.agda": [
        "module DASHI.Unified.DarkDimensionGRQuantumPromotionAdapterExact where",
        "import DASHI.Unified.GRQuantumResearchAuthorityCutset as Research",
        "import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension",
        "import DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact as Discrimination",
        "darkDimensionDoesNotPayEmpiricalCompletion",
        "phenomenologyDiscriminationDoesNotPayEmpiricalCompletion",
        "alternativeMechanismKeepsUnificationPromotionBlocked",
        "darkDimensionDoesNotPayQuantumGravityPromotion",
        "darkDimensionDoesNotPayTheoryOfEverythingPromotion",
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

print("Dark-dimension / string-theory promotion boundary static contract: OK")
