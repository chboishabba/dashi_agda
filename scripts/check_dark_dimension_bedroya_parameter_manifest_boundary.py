from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaParameterManifestBoundaryExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact where",
        "BedroyaParameterManifestStatus",
        "simulationStartRedshiftLocated",
        "fadingOnsetPhiLocated",
        "initialScaleDefinitionsLocated",
        "effectiveDMNormalizationEquationLocated",
        "onsetPhiInitialValueLocated",
        "m0n0ToRhoDM0PaperIdentityLocated",
        "rhoDM0ToSampledOmegaFDMMappingLocated",
        "v0ToSampledDarkEnergyNormalizationLocated",
        "completeNormalizationMapLocated",
        "supplementPosteriorCoordinatesDisplayed",
        "exactStandardBestFitTuplePublished",
        "normalizationMapLocated",
        "firstPartyPredecessorImplementationLocatedByCurrentSearch",
        '"1e14"',
        '"phi = 0"',
        '"rho_DM = m0 n0 exp(-cPrime phi_i) a^-3 = rho_DM^0 exp(-cPrime phi_i) a^-3"',
        '"phi_i = 0 at the stated fading onset"',
        '"m0 n0 = rho_DM^0 under phi_i = 0"',
        '"H0"',
        '"Omega_b h^2"',
        '"Omega_FDM h^2"',
        '"sigma8"',
        '"r_drag"',
        '"1906.08261"',
        "paperDMNormalizationIdentityPaid",
        "sampledOmegaFDMMappingStillOpen",
        "v0NormalizationStillOpen",
        "completeNormalizationStillOpen",
        "PaperDMIdentityEqualsSampledOmegaMapping",
        "OneNormalizationCoordinatePaysCompleteNormalization",
        "paperDMIdentityDoesNotBecomeSampledOmegaMapping",
        "partialNormalizationDoesNotCloseCompleteMap",
        "posteriorDisplayDoesNotEqualExactBestFitTuple",
        "startPrescriptionDoesNotPayNormalizationMap",
        "unlocatedImplementationDoesNotProveNonexistence",
        "exactStandardTupleStillOpen",
        "normalizationMapStillOpen",
    ],
    "DASHI/Empirical/DarkDimensionBedroyaBackgroundReconstructionExact.agda": [
        "import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest",
        "parameterManifestStillBlocksBackgroundExecution",
        "paperDMNormalizationIdentityAvailable",
        "sampledDensityMappingStillBlocksExecution",
        "v0NormalizationStillBlocksExecution",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_bedroya_parameter_manifest_boundary.py",
        "DASHI/Empirical/DarkDimensionBedroyaParameterManifestBoundaryExact.agda",
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

print("Dark-dimension Bedroya parameter-manifest boundary static contract: OK")
