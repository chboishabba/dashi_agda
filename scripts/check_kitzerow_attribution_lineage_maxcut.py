#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "public_claim": "DASHI/Core/AttributedPublicClaimExact.agda",
    "kernel": "DASHI/Core/ReopenableConsumerInterventionKernelExact.agda",
    "republication": "DASHI/Law/SolomonIslandsDefeatMotionRepublicationIndependenceExact.agda",
    "relational": "DASHI/Culture/WitchRelationalAttributionDialogueBidiExact.agda",
    "systematic": "DASHI/Wikimedia/IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact.agda",
    "priority": "DASHI/Biology/KitzerowPriorityAttributionExact.agda",
    "sota": "DASHI/Biology/KitzerowAttributionProvenanceSOTAExact.agda",
    "lineage": "DASHI/Biology/KitzerowAttributionEvidenceLineageExact.agda",
    "lineage_v": "DASHI/Biology/KitzerowAttributionEvidenceLineageValidation.agda",
    "status": "DASHI/Biology/KitzerowAttributionAcquisitionStatusExact.agda",
    "frontier": "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
    "bio_rollup": "DASHI/Biology/KitzerowBH4Everything.agda",
    "chem_rollup": "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "global_v": "DASHI/Chemistry/LineageAttributionEvidenceMaxCutValidation.agda",
}

for key, rel in paths.items():
    assert (ROOT / rel).exists(), f"missing {key}: {rel}"

text = {k: (ROOT / p).read_text() for k, p in paths.items()}

for needle in [
    "AttributedPublicClaim", "attributedMeansTrue", "authenticatedArtifactMeansInterpretationTrue",
]:
    assert needle in text["public_claim"], f"public-claim owner missing {needle}"

for needle in [
    "EvidenceIndependenceReceipt", "distinctProvenanceRoots", "noDownstreamMultiplicityInflation",
    "evidenceMultiplicityNeedsProvenanceAccounting",
]:
    assert needle in text["kernel"], f"generic evidence kernel missing {needle}"

for needle in [
    "republicationMultiplicityDoesNotAuthenticateArtifact",
    "quotedSentenceDoesNotBecomePrimaryArtifact",
    "sharedWordingDoesNotEstablishSharedSender",
]:
    assert needle in text["republication"], f"republication owner missing {needle}"

for needle in [
    "initialProvenancePreserved", "responseCreatesNewProvenance",
    "targetResponseErasesInitialProvenance", "relationalModeRequiresIndependentCoordinates",
]:
    assert needle in text["relational"], f"relational attribution owner missing {needle}"

for needle in [
    "duplicateManifestationsSeparatedFromIndependentEvidence",
    "includedCountSeparatedFromIndependentEvidenceUnits",
    "moreStudiesDoNotCreateIndependentEvidence",
]:
    assert needle in text["systematic"], f"systematic-review owner missing {needle}"

for needle in [
    "contactDoesNotProveUse", "accessDoesNotProveDerivation",
    "citationAbsenceDoesNotProvePlagiarism", "overlapScoreDoesNotCreateLegalConclusion",
]:
    assert needle in text["priority"], f"priority attribution firewall missing {needle}"

for needle in [
    "oriResearchMisconductDefinition", "copePlagiarismFlowchart", "copeRedundantPublicationFlowchart",
    "cochraneMultipleReports", "w3cProvPrimer", "crossrefSimilarityInterpretation",
    "similarityToolDeterminesPlagiarism", "similarityThresholdAutomaticallyAdjudicatesReuse",
    "guidanceAutomaticallyAdjudicatesKitzerowClaim",
    "10.24318/cope.2019.2.2", "10.24318/cope.2019.2.13",
]:
    assert needle in text["sota"], f"attribution SOTA atlas missing {needle}"

for needle in [
    "AttributionEvidenceKind", "exactTextReuse", "nearVerbatimReuse", "ideaProcessResultReuse",
    "documentedDirectUse", "canonicalKitzerowContactIndependenceReceipt",
    "downstreamPublicationMultiplicityCreatesIndependentEvidence",
    "sameProvenanceRootMayBeCountedRepeatedlyAsIndependent",
    "contactOrExposureAloneProvesDerivation", "postPublicationContactProvesPrePublicationExposure",
    "laterResponseRewritesEarlierProvenance",
    "authenticatedPrePublicationExposureAloneProvesDerivation",
    "citationAbsenceAloneProvesPlagiarism", "structuralSimilarityAloneProvesPlagiarism",
    "ideaProcessResultReuseCanBeRelevantToPlagiarism", "documentedDirectUseCanUpgradeDerivation",
    "canonicalBrazilDirectionalProvenance", "brazilNeedsEarlierExposureOrManuscriptHistory",
    "responseCreatesNewProvenanceWithoutRewritingEarlierManifestation",
    "relationalAttributionBoundary",
]:
    assert needle in text["lineage"], f"Kitzerow lineage owner missing {needle}"

for needle in [
    "republicationAndReportMultiplicityDoNotCreateIndependence",
    "contactChronologyDoesNotCollapseIntoDerivation",
    "laterReplyCreatesNewProvenanceWithoutRewritingEarlierHistory",
    "plagiarismEvidenceKindsRemainDistinct",
    "brazilPostPublicationContactCannotPayEarlierExposure",
    "similarityToolsAreDiscoveryInputsNotAdjudicators",
    "surroundingSOTAConstrainsVocabularyWithoutAdjudicatingCase",
]:
    assert needle in text["lineage_v"], f"Kitzerow lineage validation missing {needle}"

for needle in [
    "stanfordDirectionalStatus", "brazilDirectionalStatus", "iaccDirectionalStatus",
    "comparisonDerivationTraceStatus", "laterCorrespondenceCanEstablishEarlierExposure",
    "exactVersionedTraceCanUpgradeDerivationCoordinate",
    "derivationUpgradeAutomaticallyProvesPlagiarismOrLegalInfringement",
]:
    assert needle in text["status"], f"Kitzerow attribution status missing {needle}"

for needle in [
    "comparisonManuscriptHistoryArtifact", "derivationTraceArtifact",
    "publicationMultiplicitySeparateFromEvidenceIndependence",
    "postPublicationContactCannotPayEarlierExposure",
    "directUseRequiresTraceableArtifactOrManifestation",
]:
    assert needle in text["frontier"], f"global provenance frontier missing {needle}"

for needle in [
    "KitzerowAttributionProvenanceSOTAExact",
    "KitzerowAttributionEvidenceLineageExact",
    "KitzerowAttributionEvidenceLineageValidation",
    "KitzerowAttributionAcquisitionStatusExact",
]:
    assert needle in text["bio_rollup"], f"biology rollup missing {needle}"
    assert needle in text["chem_rollup"], f"chemistry rollup missing {needle}"

for needle in [
    "provenanceQueueIsDirectionAndIndependenceAware",
    "kitzerowContactReportsDoNotInflateIndependentEvidence",
    "kitzerowExposureStillDoesNotCollapseIntoDerivationOrPlagiarism",
    "brazilLaterContactDoesNotPayEarlierExposure",
    "traceableDerivationCanUpgradeWithoutAdjudicatingPlagiarism",
    "sotaGuidanceDoesNotAdjudicateTheCase",
]:
    assert needle in text["global_v"], f"global attribution validation missing {needle}"

print("Kitzerow attribution provenance-lineage / independence / temporal-direction / similarity-tool max-cut static contract: PASS")
