from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaSameObjectAcquisitionExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact where",
        "import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition",
        "import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch",
        "import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting",
        "import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage",
        "bedroya2026SameObjectTarget",
        "Acquisition.sourceAcquisitionTarget",
        "2026 Bedroya-Obied-Vafa-Wu same-fit parameter manifest and normalization map",
        "DESI+CMB+Pantheon+ negative-c best-fit chain/config or machine-readable manifest",
        "Acquisition.directDigitalArchive",
        "Acquisition.publisherBackfile",
        "bedroyaIdentitySearchDemand",
        "DebtRouting.bedroyaManifestIdentitySearchDemand",
        "childSameObjectStillUnacquired",
        "childPrimaryObjectStillUninspected",
        "childTranscriptionStillUnextracted",
        "parentLineageMayGuideSearchButCannotSubstitute",
        "parentImplementationCannotPayChildSameObjectDemand",
        "parentNormalizationCannotPayChildSameObjectDemand",
    ],
    "DASHI/Empirical/DarkDimensionResidualDebtRoutingExact.agda": [
        "bedroyaManifestIdentitySearchDemand",
        "bedroyaManifestSearchDemandRoutesToIdentityProducer",
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

print("Dark-dimension Bedroya same-object acquisition static contract: OK")
