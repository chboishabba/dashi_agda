from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaNormalizationAxisJoinExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaNormalizationAxisJoinExact where",
        "import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin",
        "import DASHI.Core.IntersectionalNonFactorability as NonFactor",
        "import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest",
        "NormalizationDependencyState",
        "paperDMOnly",
        "paperDMWithSampledDensity",
        "paperDMWithV0",
        "fullNormalization",
        "paperDMObserver",
        "sampledDensityAxis",
        "v0NormalizationAxis",
        "sampledDensityMissingWitness",
        "v0NormalizationMissingWitness",
        "paperDMObserverCannotRetainSampledDensityAxis",
        "paperDMObserverCannotRetainV0Axis",
        "paperDMObserverCannotRetainBothMissingAxes",
        "requiredNormalizationJoin",
        "paperDMIdentitySourcePaid",
        "sampledDensitySourceStillOpen",
        "v0NormalizationSourceStillOpen",
        "paidDMAxisDoesNotCompensateMissingSampledOrV0Axis",
    ],
    "DASHI/Empirical/DarkDimensionBedroyaBackgroundReconstructionExact.agda": [
        "import DASHI.Empirical.DarkDimensionBedroyaNormalizationAxisJoinExact as NormalizationJoin",
        "normalizationJoinStillBlocksBackgroundExecution",
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

print("Dark-dimension Bedroya normalization-axis join static contract: OK")
