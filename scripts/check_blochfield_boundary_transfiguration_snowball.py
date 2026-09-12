from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Culture/BoundaryConservativeTransfigurationBlochfieldExact.agda": [
        "module DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact where",
        "import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution",
        "import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as SnowballOSINT",
        "import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as Revision",
        "import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal",
        "record BoundaryConservativeTransfiguration",
        "socialCountDoesNotCreateAuthority",
        "socialCountDoesNotCreateTruth",
        "laterEvidenceDoesNotSkipUnpaidIdentity",
        '"15K"',
        '"417"',
        '"2K"',
        '"35K"',
    ],
    "DASHI/Culture/BlochfieldCreatorGenealogySnowballExact.agda": [
        "module DASHI.Culture.BlochfieldCreatorGenealogySnowballExact where",
        "creatorProfileObservation",
        '"blochfield.com"',
        '"South Atlantic Geomag. Anomaly"',
        '"Q1468412"',
        '"2026-08-28"',
        "creatorProfileLinkDoesNotPayNativeWebsite",
        "domainListingDoesNotProveCreatorOwnership",
        "southAtlanticAnomalyDoesNotPayBlochfieldTheoryLineage",
        "sameObjectTechnicalLineageStillUnpaid",
        "sameNameMediumCandidateObservation",
        '"https://medium.com/@yasminanacreto/list/80f317ad2598"',
        "crossPlatformLink3CandidateObservation",
        '"https://link3.to/0xyasanacreto"',
        "crossPlatformIdentityWeld",
        "sameDisplayNameDoesNotPaySamePerson",
        "handleStemDoesNotPaySamePerson",
    ],
    "DASHI/Culture/BlochfieldCrossPlatformIdentityConvergenceExact.agda": [
        "module DASHI.Culture.BlochfieldCrossPlatformIdentityConvergenceExact where",
        "link3XGalacticGConvergenceCandidate",
        '"What\'s a Galactic G?"',
        '"@Galxe"',
        '"@gmnevergiveup"',
        "galacticGToGmNeverGiveUpRelationPaidIsFalse",
        "galacticGDoesNotPayGmNeverGiveUpRelation",
        "multiCoordinateConvergenceDoesNotPaySamePerson",
        "crossPlatformIdentityWeldStillUnpaid",
    ],
    "DASHI/Culture/BlochfieldHistoricalWalletReviewCandidateExact.agda": [
        "module DASHI.Culture.BlochfieldHistoricalWalletReviewCandidateExact where",
        "fewchaWalletReviewObservation",
        "historicalWalletReviewCandidate",
        '"2024-05-08"',
        '"Fewcha Move Wallet"',
        '"Yasmin Anacreto"',
        "sameNameWalletReviewDoesNotPaySamePerson",
        "walletUseContextDoesNotPayAccountOwnership",
        "crossPlatformIdentityWeldStillUnpaid",
    ],
    "DASHI/Culture/BlochfieldMediumSavedReadingSnowballExact.agda": [
        "module DASHI.Culture.BlochfieldMediumSavedReadingSnowballExact where",
        "darkMatterLabsRadicleCivicsSource",
        "mediumSavedRadicleCivicsCandidate",
        "savedReadingDoesNotPayCreatorLineage",
        "sameNameMediumIdentityStillUnpaid",
        "creatorLongFormStillUnpaid",
        '"Radicle Civics — Building Proofs of Possibilities for a Civic Economy and Society"',
        '"https://provocations.darkmatterlabs.org/radicle-civics-building-proofs-of-possibilities-for-a-civic-economy-and-society-ee28baeeec70"',
        '"2023"',
    ],
    "DASHI/Culture/BlochfieldAcquisitionResidualSnowballExact.agda": [
        "module DASHI.Culture.BlochfieldAcquisitionResidualSnowballExact where",
        "exactPhraseSearchNonLocation",
        "searchNonLocationDoesNotProveAbsence",
        "reverseTopologicalAnalogueCandidate",
        "conceptualResemblanceDoesNotCreateLineage",
        "nativeCreatorMaterialStillFirstPayingLeaf",
        '"2090447851625050481"',
        '"protects change from becoming epistemically destructive"',
        '"10.1016/j.physb.2026.418616"',
    ],
    "DASHI/Culture/Everything.agda": [
        "import DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact",
        "import DASHI.Culture.BlochfieldCreatorGenealogySnowballExact",
        "import DASHI.Culture.BlochfieldCrossPlatformIdentityConvergenceExact",
        "import DASHI.Culture.BlochfieldHistoricalWalletReviewCandidateExact",
        "import DASHI.Culture.BlochfieldMediumSavedReadingSnowballExact",
        "import DASHI.Culture.BlochfieldAcquisitionResidualSnowballExact",
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
            missing.append(f"{rel}: missing {needle!r}")

if missing:
    raise SystemExit("\n".join(missing))

print("blochfield boundary-transfiguration snowball static check: ok")
