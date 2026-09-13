from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionResidualDebtRoutingExact.agda": [
        "module DASHI.Empirical.DarkDimensionResidualDebtRoutingExact where",
        "import DASHI.Core.ProofDebtRouterExact as ProofDebt",
        "import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch",
        "import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search",
        "import DASHI.Empirical.DarkDimensionDAOSameKeyReconstructionRunExact as DAORun",
        "import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as BedroyaManifest",
        "daoFormalCertificationRoute",
        "ProofDebt.certificationDebt",
        "daoExecutionStillOpen",
        "bedroyaFirstMissingSourceCoordinate",
        "SourceSearch.sameObjectUnresolved",
        "bedroyaSameObjectGapRoutesToIdentityProducer",
        "Search.identityProducer",
        "daoExecutionCannotPayBedroyaAcquisitionGap",
        "certificationCannotPayMissingSourceIdentity",
        "bedroyaAcquisitionStillOpen",
        "residualKindsRemainDistinct",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting",
        "residualDebtClassesRemainDistinct",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_residual_debt_routing.py",
        "DASHI/Empirical/DarkDimensionResidualDebtRoutingExact.agda",
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

print("Dark-dimension residual debt routing static contract: OK")
