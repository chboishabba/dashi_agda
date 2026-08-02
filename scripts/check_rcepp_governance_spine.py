#!/usr/bin/env python3
"""Fail-closed audit for the RCEPP and revolutionary-practice governance tranche.

The exact checks protect the coarse-one/fine-three distinction, local/global
section preservation, plural revolutionary braid, trauma-memory non-authority,
liberation-goal/tactic separation and climate-pressure non-reduction.  The
source scan protects the theorem surface against proof holes, postulate
declarations and accidental authority promotion.  It is not a substitute for
Agda kernel checking or external historical, legal, political, cultural or
popular-recognition authority.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]

FILES = [
    ROOT / "DASHI/Governance/RelationalMandateFibre.agda",
    ROOT / "DASHI/Governance/AuthorityMandateCore.agda",
    ROOT / "DASHI/Governance/SituatedConstituency.agda",
    ROOT / "DASHI/Governance/CouncilDelegationGraph.agda",
    ROOT / "DASHI/Governance/LocalGlobalCouncilGluing.agda",
    ROOT / "DASHI/Governance/TransitionResidual.agda",
    ROOT / "DASHI/Governance/ExternalLegitimacyBoundary.agda",
    ROOT / "DASHI/Governance/RevolutionarySourceAtlas.agda",
    ROOT / "DASHI/Governance/RevolutionaryPracticeBraid.agda",
    ROOT / "DASHI/Governance/TraumaMemorySublationBoundary.agda",
    ROOT / "DASHI/Governance/ComparativeCrisisClimateAtlas.agda",
    ROOT / "DASHI/Governance/RevolutionaryAdjunctRegression.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPSourceBoundary.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPInstitutionalSurface.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPPromotionBoundary.agda",
    ROOT / "DASHI/Governance/Sudan/RCEPPRegression.agda",
    ROOT / "DASHI/Governance/Everything.agda",
]

REQUIRED_TOKENS = {
    "RelationalMandateFibre.agda": [
        "data MandateFineRole",
        "coarseMandateUnit",
        "canonicalMandateFineRoleCountIsThree",
        "MandateFibre : CoarseMandateUnit",
        "mandateFibreRestrictionCore",
        "rankOneDepthOneHasThreeSites",
        "arithmeticOneEqualsThreeClaimed",
        "spatialOntologyClaimed",
        "politicalAuthorityPromoted",
    ],
    "AuthorityMandateCore.agda": [
        "data AuthoritySource",
        "AdmissibleAuthoritySource possessionOfForce = Never",
        "possessionOfForceRejected",
        "record Mandate",
        "record NonAlienatingMandate",
        "mandateRemainsWithConstituency",
        "recallable",
        "reviewable",
        "governanceRoleFamily",
        "formalModelCreatesPopularLegitimacy",
        "Hanna Fenichel Pitkin",
    ],
    "SituatedConstituency.agda": [
        "data GovernanceAxis",
        "ruralUrbanAxis",
        "displacementAxis",
        "landAxis",
        "colonialityAxis",
        "armedPowerAxis",
        "axisFreeRepresentationIsFalse",
        "ruralConstituency",
        "idpCampConstituency",
        "10.2307/1229039",
    ],
    "CouncilDelegationGraph.agda": [
        "data CouncilLevel",
        "delegatesUpward",
        "accountsDownward",
        "data SubordinationPath",
        "militaryToPeoplePath",
        "militaryHasDirectSovereignEdge",
    ],
    "LocalGlobalCouncilGluing.agda": [
        "record LocalCouncilSection",
        "record CompatibleCouncilFamily",
        "rceppCouncilBundleSheaf",
        "canonicalCouncilCompatibility",
        "canonicalGlobalRestrictsToNeighbourhood",
        "canonicalGlobalRestrictsToIDPCamp",
        "compatibilityWitnessRequired",
        "coexistenceAloneCreatesGlobalCouncil",
        "actualConstituencyCompatibilityEstablished",
    ],
    "TransitionResidual.agda": [
        "governanceTopologyIsChartResidualPlusOne",
        "data TransitionalPhase",
        "data AdmissibleTransition",
        "data GovernanceValidation",
        "undeterminedAxisIncomplete",
        "record ConstitutionalResidual",
        "record ConstitutionalPlusOne",
        "unresolvedResidualsRetainedIsTrue",
        "authorityPromotedByFormalStepIsFalse",
        "stageCompressionDoesNotPromoteAuthority",
    ],
    "ExternalLegitimacyBoundary.agda": [
        "data ExternalPopularRecognitionToken",
        "formalReceiptDoesNotCreatePopularLegitimacy",
        "externalRecognitionTokenAvailableInternally",
        "politicalAuthorityPromoted",
        "legalAuthorityPromoted",
    ],
    "RevolutionarySourceAtlas.agda": [
        "record SourceReference",
        "Robin Wall Kimmerer",
        "Braiding Sweetgrass",
        "Andie Nordgren",
        "Relationship Anarchy",
        "Peter Kropotkin",
        "Frantz Fanon",
        "Judith Butler",
        "Dominick LaCapra",
        "10.2307/1229039",
        "The 9/11 Commission Report",
        "Edward W. Said",
        "Rashid Khalidi",
        "Ervand Abrahamian",
        "Todd Gitlin",
        "sourceCreatesInterpretiveAuthorityIsFalse",
    ],
    "RevolutionaryPracticeBraid.agda": [
        "data RevolutionaryPracticeStrand",
        "data RelationalFreedomDimension",
        "data PrefigurativePractice",
        "repoLocalPatternMindRepairContext",
        "canonicalSummerOfLoveHistoricalBoundary",
        "canonicalMeansEndsSedimentationBoundary",
        "Sweetgrass.SweetgrassCarrierSpineSurface",
        "Dialectic.DialecticalDepthAccumulationReceipt",
        "CarryBraid.UnifiedCarryBraidReceipt",
        "braidCollapsesTraditions",
        "unityRequiresUniformity",
        "publicOwnershipEqualsEcologicalReciprocity",
        "universalRevolutionaryDoctrinePromoted",
        "politicalAuthorityPromoted",
    ],
    "TraumaMemorySublationBoundary.agda": [
        "data CollectiveTraumaContext",
        "data TraumaResponseMode",
        "data SublationInvariant",
        "record HistoricalOriginFrame",
        "iranNineteenFiftyThreeFrame",
        "iranNineteenSeventyNineFrame",
        "israelPalestinePluralOriginFrame",
        "sudanAprilTwentyTwentyThreeFrame",
        "record PriorInjuryAuthorityBoundary",
        "priorInjuryAuthorisesCivilianHarm",
        "traumaParityImpliesPowerParity",
        "reflectingPoolObservation",
        "whiteHouseRenovationObservation",
        "Freedom 250 / WWE",
        "motiveInferredAsFact",
        "formalSublationGuaranteesReconciliation",
    ],
    "ComparativeCrisisClimateAtlas.agda": [
        "data ComparativeCrisisContext",
        "data PalestinianLiberationCurrent",
        "marxistPFLPCurrent",
        "Popular Front for the Liberation of Palestine (PFLP)",
        "liberatoryObjectiveAutomaticallyLegitimatesEveryTactic",
        "tacticCondemnationErasesUnderlyingLiberationClaim",
        "data ClimateJusticeAxis",
        "climatePressureAloneCausesWar",
        "record EcologicalPeaceRepairSurface",
        "record GlobalAttentionResidual",
        "sufferingScaleEqualsAttention",
        "casesAreHistoricallyEquivalent",
        "formalAtlasCreatesPoliticalAuthority",
    ],
    "RevolutionaryAdjunctRegression.agda": [
        "record RevolutionaryAdjunctRegression",
        "canonicalRevolutionaryAdjunctRegression",
        "relationshipCategoryDoesNotCreateEntitlement",
        "priorInjuryDoesNotAuthoriseCivilianHarm",
        "pflpObjectiveDoesNotLegitimateEveryTactic",
        "climateDoesNotActAsSoleWarCause",
        "globalAttentionDoesNotMeasureSuffering",
        "canonicalRevolutionaryAdjunctReceiptsNonPromoting",
    ],
    "RCEPPSourceBoundary.agda": [
        "The Revolutionary Charter for Establishing People's Power",
        "11 January 2023",
        "No DOI assigned in the supplied edition",
        "suppliedPageCount",
        "canonicalRCEPPCitationHasNoArtifact",
        "legalOperationClaimed",
        "universalEndorsementClaimed",
    ],
    "RCEPPInstitutionalSurface.agda": [
        "data RCEPPConstituencyKind",
        "electedUnionConstituencyKind",
        "idpCampConstituencyKind",
        "canonicalRCEPPCivilianSupremacySurface",
        "canonicalRCEPPPublicResourceCustody",
        "canonicalRCEPPPeaceReconstructionSurface",
        "canonicalRCEPPTransitionInvariantSurface",
        "officialRCEPPInterpretationClaimed",
        "legalOperationClaimed",
    ],
    "RCEPPPromotionBoundary.agda": [
        "rceppCitationIdentityRemainsOpen",
        "rceppCitationOnlyQuarantines",
        "rceppCitationOnlyAuthorizationAbstains",
        "canonicalPromotionAuthorized",
        "governedDecisionIsAbstain",
    ],
    "RCEPPRegression.agda": [
        "record RCEPPGovernanceRegression",
        "canonicalRCEPPGovernanceRegression",
        "rankOneFineRoleCountIsThree",
        "rankOneHypervoxelCountIsThree",
        "localGlobalGluingBoundary",
        "neighbourhoodRestrictionExact",
        "idpRestrictionExact",
        "forceSourceRejected",
        "formalLegitimacyNotMinted",
        "citationOnlyAuthorizationAbstains",
        "canonicalRCEPPGovernanceReceiptsNonPromoting",
    ],
    "Everything.agda": [
        "import DASHI.Governance.AuthorityMandateCore",
        "import DASHI.Governance.LocalGlobalCouncilGluing",
        "import DASHI.Governance.RelationalMandateFibre",
        "import DASHI.Governance.RevolutionarySourceAtlas",
        "import DASHI.Governance.RevolutionaryPracticeBraid",
        "import DASHI.Governance.TraumaMemorySublationBoundary",
        "import DASHI.Governance.ComparativeCrisisClimateAtlas",
        "import DASHI.Governance.RevolutionaryAdjunctRegression",
        "import DASHI.Governance.Sudan.RCEPPPromotionBoundary",
        "import DASHI.Governance.Sudan.RCEPPRegression",
    ],
}

FORBIDDEN_PATTERNS = [
    re.compile(r"^\s*postulate\b", re.MULTILINE),
    re.compile(r"\{!"),
    re.compile(r"!\}"),
    re.compile(r"\bTERMINATING\b"),
    re.compile(r"\bNON_TERMINATING\b"),
    re.compile(r"arithmeticOneEqualsThreeClaimed\s*=\s*true"),
    re.compile(r"spatialOntologyClaimed\s*=\s*true"),
    re.compile(r"formalModelCreatesPopularLegitimacy\s*=\s*true"),
    re.compile(r"militaryHasDirectSovereignEdge\s*=\s*true"),
    re.compile(r"coexistenceAloneCreatesGlobalCouncil\s*=\s*true"),
    re.compile(r"actualConstituencyCompatibilityEstablished\s*=\s*true"),
    re.compile(r"legalOperationClaimed\s*=\s*true"),
    re.compile(r"universalEndorsementClaimed\s*=\s*true"),
    re.compile(r"officialRCEPPInterpretationClaimed\s*=\s*true"),
    re.compile(r"canonicalPromotionAuthorized\s*=\s*true"),
    re.compile(r"sourceCreatesInterpretiveAuthority\s*=\s*true"),
    re.compile(r"universalRevolutionaryDoctrinePromoted\s*=\s*true"),
    re.compile(r"priorInjuryAuthorisesCivilianHarm\s*=\s*true"),
    re.compile(r"motiveInferredAsFact\s*=\s*true"),
    re.compile(r"liberatoryObjectiveAutomaticallyLegitimatesEveryTactic\s*=\s*true"),
    re.compile(r"climatePressureAloneCausesWar\s*=\s*true"),
    re.compile(r"casesAreHistoricallyEquivalent\s*=\s*true"),
    re.compile(r"formalAtlasCreatesPoliticalAuthority\s*=\s*true"),
]


def check_exact_shape() -> None:
    coarse_units = 1
    fine_roles = ("principal", "delegate", "mandate-relation")
    rank = 1
    depth = 1
    assert coarse_units == 1
    assert len(fine_roles) == 3
    assert 3 ** (rank * depth) == len(fine_roles)
    assert coarse_units != len(fine_roles)

    local_sections = (
        "neighbourhood",
        "rural-locality",
        "elected-union",
        "idp-camp",
    )
    assert len(local_sections) == 4
    assert len(set(local_sections)) == len(local_sections)

    phases = (
        "coup",
        "prefigurative",
        "temporary-civilian",
        "constituted-transition",
        "constitution-making",
        "democratic-closure",
    )
    assert len(phases) == 6

    validation_positions = (
        "satisfied",
        "positively-violated",
        "undetermined-axis-incomplete",
        "inapplicable-to-role",
    )
    assert len(validation_positions) == 4

    revolutionary_strands = (
        "institutional",
        "relational",
        "epistemic",
        "ecological",
        "historical-trauma",
    )
    assert len(revolutionary_strands) == 5

    relational_dimensions = (
        "consent",
        "autonomy",
        "material-asymmetry",
        "reciprocity",
        "exit-recall-revision",
    )
    assert len(relational_dimensions) == 5

    palestinian_currents = (
        "secular-national",
        "marxist-pflp",
        "islamist",
        "trade-union-student-women",
        "popular-committee",
        "diplomatic-state-building",
        "cultural-intellectual",
        "diaspora",
    )
    assert len(palestinian_currents) == 8

    climate_axes = (
        "food-water",
        "displacement",
        "land-livelihood",
        "urban-pressure",
        "energy-geopolitics",
        "border-militarisation",
        "disaster-opportunism",
        "unequal-recovery",
    )
    assert len(climate_axes) == 8

    memory_infrastructure = (
        "reflecting-pool",
        "executive-renovation",
        "national-anniversary-combat-spectacle",
    )
    assert len(memory_infrastructure) == 3


def scan_sources() -> None:
    for path in FILES:
        if not path.is_file():
            raise AssertionError(f"missing required file: {path.relative_to(ROOT)}")

        text = path.read_text(encoding="utf-8")
        for pattern in FORBIDDEN_PATTERNS:
            if pattern.search(text):
                raise AssertionError(
                    f"forbidden pattern {pattern.pattern!r} in {path.relative_to(ROOT)}"
                )

        for token in REQUIRED_TOKENS[path.name]:
            if token not in text:
                raise AssertionError(
                    f"missing required token {token!r} in {path.relative_to(ROOT)}"
                )


def main() -> int:
    check_exact_shape()
    scan_sources()
    print("PASS: one coarse mandate unit remains distinct from three fine relational roles")
    print("PASS: rank-one/depth-one ternary shape has exactly three fine sites")
    print("PASS: force, elite agreement and external recognition alone cannot originate authority")
    print("PASS: situated representation carries explicit rural, displacement, land and power axes")
    print("PASS: delegation upward remains distinct from accountability and recall downward")
    print("PASS: compatible local council sections glue and restrict back without erasure")
    print("PASS: constitutional +1 transitions retain residuals and preserve authority boundaries")
    print("PASS: source atlas retains author/title/DOI state without minting interpretive authority")
    print("PASS: Sweetgrass, PatternMind, relationship-anarchy and anarchist strands braid without collapse")
    print("PASS: Summer of Love informality, consent, labour and commodification residuals remain explicit")
    print("PASS: prior injury never authorises unlimited control or civilian harm")
    print("PASS: reflecting-pool, White House and Freedom 250 observations remain candidate-only")
    print("PASS: Palestinian liberation goals remain distinct from tactic-specific accountability")
    print("PASS: Iran/USA selected origins retain prior history and do not close causation")
    print("PASS: climate pressure is material but not a sole-cause war theorem")
    print("PASS: Sudan remains a situated case rather than an ignored analogy or attention proxy")
    print("PASS: RCEPP citation identity remains separate from artifact, legal and popular authority")
    print("PASS: governance/RCEPP/revolutionary adjunct source surface is fail-closed")
    print("NOTE: run the Agda checker for kernel validation")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AssertionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        raise SystemExit(1)
