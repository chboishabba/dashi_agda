from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaSameObjectAcquisitionExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaSameObjectAcquisitionExact where",
        "import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition",
        "import DASHI.Core.BidiResidualApproximationExact as Bidi",
        "import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SourceSearch",
        "import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search",
        "import DASHI.Empirical.DarkDimensionResidualDebtRoutingExact as DebtRouting",
        "import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage",
        "bedroya2026SameObjectTarget",
        "bedroyaIdentitySearchDemand",
        "CandidateCustody",
        "childSpecificManifest",
        "parentOnlyImplementation",
        "ancestorParameterizationOnly",
        "candidateCustodyPrior",
        "sameObjectIdentityMeasurement",
        "bedroyaSameObjectSearchExperiment",
        "exactChildObservationWouldRefineCustody",
        "lineageOnlyObservationWouldRefineCustody",
        "lineageOnlyObservationDoesNotIdentifyCustody",
        "bedroyaPostIdentitySupportGap",
        "SourceSearch.propositionSupportUnresolved",
        "bedroyaPostIdentitySupportDemand",
        "Search.propositionSourceProducer",
        "postIdentitySupportStillRequiresSourcePayment",
        "bedroyaSampledDensityMappingDemand",
        "rho_DM^0 to sampled Omega_FDM h^2 correspondence",
        "bedroyaV0NormalizationDemand",
        "V0 to fitted dark-energy normalization correspondence",
        "sampledDensityAndV0DemandsRemainDistinct",
        "sameObjectLocationDoesNotCloseSupport",
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
