from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDAOParameterManifestBoundaryExact.agda": [
        "module DASHI.Empirical.DarkDimensionDAOParameterManifestBoundaryExact where",
        "DAOParameterManifestStatus",
        "exampleInputLocated",
        "retrospectiveDESIConfigLocated",
        "bestFitRowLocated",
        "repositoryVersionLinkedToIndependentTarget",
        "pinnedSnapshotPostdatesIndependentPaper",
        "snapshotChronologyPaysPaperManifest",
        "independentTargetSpecificConfigLocated",
        "bestFitRowSourceBoundToIndependentTarget",
        "independentTargetExecutableManifestFrozen",
        "input/DRMD.ini",
        "cobaya/DRMD.yaml",
        "notebooks/DRMD/DRMD.bestfit",
        "bao.desi_dr2",
        "2602.23895",
        "2026-02-27",
        "2026-06-04",
        '"13.05733"',
        '"7"',
        "bestFitRowMatchesPaperFixedInteractionStrength",
        "publicBestFitInteractionCoordinateMismatchRecorded",
        "publicBestFitCannotBeIndependentPaperBestFit",
        "parameterManifestHash",
        "exampleInputDoesNotBecomePaperPrediction",
        "desiConditionedFitDoesNotBecomeHeldOutPrediction",
        "ambiguousBestFitRowDoesNotPayIndependentManifest",
        "versionLinkDoesNotManufactureSpecificConfig",
        "laterSnapshotDoesNotCertifyPaperManifest",
        "independentTargetConfigStillOpen",
        "independentTargetManifestStillOpen",
    ],
    "DASHI/Empirical/DarkDimensionDAOSameKeyExtractionRecipeExact.agda": [
        "import DASHI.Empirical.DarkDimensionDAOParameterManifestBoundaryExact as Manifest",
        "parameterManifestStillBlocksExecutionClaim",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_dao_parameter_manifest_boundary.py",
        "DASHI/Empirical/DarkDimensionDAOParameterManifestBoundaryExact.agda",
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

print("Dark-dimension DAO parameter-manifest boundary static contract: OK")
