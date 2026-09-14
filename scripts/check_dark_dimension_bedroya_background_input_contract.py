from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaBackgroundInputContractExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaBackgroundInputContractExact where",
        "import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as Background",
        "import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest",
        "BedroyaBackgroundInputStatus",
        "backgroundEquationsLocated",
        "cBestFitLocated",
        "cPrimeBestFitLocated",
        "simulationStartLocated",
        "phiInitialLocated",
        "paperDMNormalizationLocated",
        "exactH0SameFitLocated",
        "exactOmegaR0Located",
        "exactOmegaB0SameFitLocated",
        "sampledDMNormalizationMappingLocated",
        "v0NormalizationLocated",
        "initialScalarVelocityConventionLocated",
        "exactRDragSameFitLocated",
        "completeBackgroundInputManifestLocated",
        "canonicalBedroyaBackgroundInputStatus",
        "partialInputSurfacePaid",
        "initialVelocityConventionStillOpen",
        "exactRDragSameFitStillOpen",
        "completeBackgroundInputStillOpen",
        "HubbleFrozenMeansExactZeroInitialVelocity",
        "PosteriorCoordinateDisplayedMeansExactSameFitInput",
        "BackgroundHVectorPaysBAOWithoutRDrag",
        "hubbleFrozenDoesNotManufactureExactInitialVelocity",
        "displayedPosteriorDoesNotManufactureExactSameFitInput",
        "backgroundHVectorDoesNotPayBAOWithoutRDrag",
    ],
    "DASHI/Empirical/DarkDimensionBedroyaSameObjectAcquisitionExact.agda": [
        "bedroyaInitialScalarVelocityConventionDemand",
        "initial scalar velocity convention used by the 2026 CLASS implementation",
        "bedroyaRDragSameFitDemand",
        "exact same-fit r_drag used for the 2026 DESI BAO prediction surface",
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

print("Dark-dimension Bedroya background-input contract: OK")
