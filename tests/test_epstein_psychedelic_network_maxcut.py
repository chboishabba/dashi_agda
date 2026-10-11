from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

EXPECTED = {
    "DASHI/Cognition/EpsteinPsychedelicSourceAtlasExact.agda": [
        "EFTA02458524",
        "EFTA00814480",
        "EFTA01054265",
        "EFTA00692098",
        "EFTA01052096",
        "EFTA00984125",
        "EFTA00862301",
        "EFTA00821182",
        "EFTA00820611",
        "EFTA00818930",
        "EFTA00984429",
        "EFTA00865569",
        "Rick Doblin",
        "ibogaine",
        "scopolamine",
        "transferStatementEqualsBankSettlement",
        "fundingInstructionEqualsCompletedPayment",
    ],
    "DASHI/Cognition/EpsteinPsychedelicNetworkEvidenceExact.agda": [
        "EvidenceGradedGenealogyCore",
        "directDocumentedTransfer",
        "fundingOrganisationalLink",
        "oneStrongEdgeDoesNotEstablishUniversalNetwork",
        "documentedInterestDoesNotEstablishAdministration",
        "yuAttributesEpsteinBrokerage",
        "kuhnIntroductionReceipt",
        "jointCommunityConveningProposal",
        "epsteinFundingSpecialAbilitySearch",
    ],
    "DASHI/Cognition/EpsteinPsychedelicParetoSnowballExact.agda": [
        "SensibLawFiniteRequirementParetoFrontierExact",
        "GinoYuCorpus",
        "DoblinMAPSIntersection",
        "ChomskyLanguageAIDispute",
        "DoblinPublicBenefitGovernance",
        "ScopolamineTrumpetSameObject",
        "paretoRoutingCreatesTruth",
    ],
    "DASHI/Cognition/EpsteinPsychedelicNeuroforecastingCrossPollinationExact.agda": [
        "NeuralRepresentationLaplacianExact",
        "Motoki",
        "facebookVideoAds",
        "socialRelatedNeuralMeasureForecastsAggregateSharing",
        "forecastDoesNotEstablishMechanism",
        "facebookResultDoesNotEstablishInstagramDeployment",
        "neuroforecastingDoesNotEstablishEpsteinYuUse",
    ],
    "DASHI/Cognition/DoblinMAPSPublicBenefitPrivateProfitExact.agda": [
        "Psychedelic Alpha",
        "Rick Doblin",
        "authorSelfReport",
        "selfReportDoesNotIndependentlyVerify",
        "publicBenefitPrivateProfitTension",
        "mapsPBCWhollyOwnedClaim",
    ],
    "DASHI/Cognition/ChomskyLanguageAIDisputeExact.agda": [
        "ConsentDistrustDualityExact",
        "povertyOfStimulus",
        "competencePerformanceDistinction",
        "generativeCapacity",
        "PoSHBench",
        "innateSyntaxOnlyRouteChallenged",
        "llmSuccessDoesNotEstablishHumanMechanism",
        "llmFailureDoesNotProveUniversalGrammar",
    ],
    "DASHI/Cognition/EpsteinPsychedelicNetworkValidation.agda": [
        "canonicalEpsteinPsychedelicBoundary",
        "currentEpsteinPsychedelicRoute",
        "fundingSettlementStillOpen",
        "kuhnIntroductionObserved",
        "conveningProposalNotCompletion",
    ],
}


def test_epstein_psychedelic_network_surface_exists_and_keeps_boundaries():
    for rel, needles in EXPECTED.items():
        path = ROOT / rel
        assert path.exists(), f"missing production owner: {rel}"
        text = path.read_text(encoding="utf-8")
        for needle in needles:
            assert needle in text, f"{needle!r} missing from {rel}"


def test_cognition_rollup_exports_epstein_psychedelic_network():
    rollup = (ROOT / "DASHI/Cognition/Everything.agda").read_text(encoding="utf-8")
    for module in EXPECTED:
        module_name = module.removesuffix(".agda").replace("/", ".")
        assert f"import {module_name}" in rollup
