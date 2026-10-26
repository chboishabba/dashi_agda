"""Australian political economy cross-PR same-object provenance contracts.

Source-text tests are not Agda kernel checks or evidence that an event occurred.
Parent Auspol owners are reused; unmerged governance sibling #1251 is not imported.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
ADAPTER = ROOT / "DASHI/Cognition/AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact.agda"
CASE = ROOT / "DASHI/Cognition/AquinoMaxwellEpsteinCAMaxCutExact.agda"
DOC = ROOT / "docs/research/AustralianPoliticalEconomyCrossNetworkMaxCut20261026.md"


def test_all_existing_parent_auspol_owners_reused_without_sibling_import():
    s = ADAPTER.read_text()
    expected = (
        "AustraliaRinehartTrumpOneNationAccessBridgeExact as Access",
        "QueenslandRinehartCrisafulliTrumpResourceAccessExact as QLD",
        "AustraliaMandelsonMiningTaxPoliticalEconomyBridgeExact as Tax",
        "EpsteinAustraliaEliteNetworkAcquisitionExact as Australia",
        "BannonFaragePalmerAutomatedInfluenceReceiptsExact as Palmer",
    )
    for symbol in expected:
        assert symbol in s
    assert "import DASHI.Governance.AustralianPoliticalRadioInfluence2026Exact" not in s
    assert "import DASHI.Governance.ClimateGenealogyTypedCasesExact" not in s
    assert "oneNationAccessOwner = Access.canonicalAustraliaTrumpPoliticalFinanceBoundary" in s
    assert "queenslandResourceOwner = QLD.canonicalQueenslandResourceAccessBoundary" in s
    assert "australianMiningTaxOwner = Tax.canonicalMiningTaxPoliticalEconomyBoundary" in s


def test_first_person_policy_and_document_origins_separate():
    s = ADAPTER.read_text()
    for token in (
        "hansonFloridaFlightsSenateDeclaration = australia-source-role-receipt",
        "2025-12-16",
        "Hancock Prospecting and Rinehart hospitality",
        "PDF original face 403",
        "hansonPolicyConsultationABC = australia-source-role-receipt",
        "hansonSpecificPensionerPolicyOriginalTranscript = australia-source-role-receipt",
        "hansonAttributedSpecificPensionerPolicyOrigin = refl",
        "oneNationJan15_2025PrimaryPolicyPublication = australia-source-role-receipt",
        "oneNationOriginalPartyPensionerPolicyPublished = refl",
        "noDatedPrePublicationRinehartInstructionInspected = refl",
        "partyElectionPledgeNotAutomaticallyEnactedCommonwealthLaw = refl",
        "aecSecondHalf2026TransitionOriginal = australia-source-role-receipt",
        "aecSecond2026TransitionPublicationNotFirstFYRelease = refl",
        "hansonAircraftCorporateStatement = australia-source-role-receipt",
        "namedAssociatesOneNationCashSupport = australia-source-role-receipt",
        "hancockIPA2016And2017JudicialDocument = australia-source-role-receipt",
        "AUD 2.3m 2016 + AUD 2.2m 2017",
        "JUDGMENT reproduces",
        "bannonPalmerContrarySourceReceipt = australia-source-role-receipt",
        "palmerRevisedContactAttribution = australia-source-role-receipt",
        "palmerLaterSingleCallSourceAttributed = refl",
        "palmerCampaignDirectionNotIndependentlyVerified = refl",
        "EFTA01615861",
        "brief unsolicited call",
        "Palmer denies",
    ):
        assert token in s


def test_2026_aec_publication_ceiling_and_no_retroactive_2027_reform():
    s = ADAPTER.read_text()
    doc = DOC.read_text()
    for token in (
        "aecOldRegimeAnnualDisclosureGate = australia-source-role-receipt",
        "aecDisclosure2026PublicationOriginal = australia-source-role-receipt",
        "2026-11-17",
        "2027-02-01",
        "2027-01-01",
        "2027-03-11",
        "2027-04-22",
        "2025-01-15",
        "futureReformMustNotRetrospectivelyRewrite2026 = refl",
        "noCurrentAECAnnualReturnWithoutPublication = refl",
    ):
        assert token in s
    for token in (
        "20 October 2026",
        "17 November 2026",
        "1 February 2027",
        "$17,300",
        "$5,000",
        "2027",
        "different SA 2026",
    ):
        assert token.lower() in doc.lower()


def test_case_imports_thin_source_owner_and_keeps_nonpromotion():
    c = CASE.read_text()
    for token in (
        "import DASHI.Cognition.AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact as Auspol",
        "canonicalAuspolSameObjectOwner = Auspol.canonicalAustralianPowerPipelineFrontier",
        "auspolMaterialSupportActuallyPaidAtReportedScope = refl",
        "auspolSpecificIPAEditorialOrderNotPaid = refl",
        "auspolRinehartEpsteinDirectEdgeNotPaid = refl",
        "auspolKoganUKUSScoresNotAssumedAustralianDeployment = refl",
        "auspolNoCommonGlobalCommand = refl",
    ):
        assert token in c


def test_record_positional_values_are_fail_closed():
    s = ADAPTER.read_text()
    a = s.index("record AustralianPowerPipelineFrontier : Set where")
    b = s.index("open AustralianPowerPipelineFrontier public", a)
    names = re.findall(r"^    (\w+) : Bool$", s[a:b], re.M)
    assert len(names) == 20
    p = s.index("canonicalAustralianPowerPipelineFrontier = australian-power-pipeline-frontier", b)
    q = s.index("\n\n", p)
    vals = re.findall(r"\b(?:true|false)\b", s[p:q])
    assert len(vals) == len(names)
    mapping = dict(zip(names, vals))
    for k in (
        "materialSupportAndFirstPersonPolicyAdvicePresent",
        "originalParliamentaryFlightDisclosureIdentified",
        "courtReportedHancockIPAPaymentsPresent",
        "namedAssociateDonationsDistinctFromAircraft",
        "bannonPalmerStatementAndDenialPreserved",
        "mandelsonStrategyReachedEpsteinAtSourceScope",
        "hansonAttributesSpecificPensionerWorkProposalToRinehart",
        "oldFY2025_26AECAnnualDisclosurePublicationPending",
        "oneNationJan2025PensionerPolicyOfficiallyPublished",
        "aecJulDec2026OldRegimeReturnPublicationPending",
    ):
        assert mapping[k] == "true"
    for k in (
        "publishedDonorAnnualReturnSameAsReportedAprilDonation",
        "originalRinehartPolicyInstructionBeforeJan2025Authenticated",
        "pensionerPolicyEnactedInCommonwealthLawVerified",
        "aecFutureReformThresholdApplicableRetroactively",
        "oneNationInternalPolicyAdoptionCausallyProven",
        "specificIPAContentBoughtByCourtReportedPayments",
        "directRinehartEpsteinRelationProven",
        "AustralianCampaignUsedKoganRiponScoresProven",
        "QueenslandFastTrackCausedByRinehartConsultationProven",
        "wholeAustraliaUSCovertCommandProven",
    ):
        assert mapping[k] == "false"


def test_sibling_climate_funding_not_promoted_to_epstein_rinehart_or_ipa_editorial_orders():
    s = ADAPTER.read_text()
    d = DOC.read_text()
    for term in (
        "siblingClimateFinanceOwnershipNote",
        "unmerged master sibling",
        "specificIPAContentBoughtByCourtReportedPayments",
        "rinaDirectEpsteinConnectionNotEstablished = refl",
        "policyConsultationNotPartyControl = refl",
        "bannonStatementNotIndependentPalmerDirection = refl",
    ):
        assert term in s
    for term in (
        "1969 tobacco",
        "1998 API",
        "HPPL→IPA",
        "not",
        "H3 remains",
    ):
        assert term.lower() in d.lower()


def test_palmer_versioned_attribution_and_same_message_original_not_duplicated():
    s = ADAPTER.read_text()
    d = DOC.read_text()
    parent = (ROOT / "DASHI/Cognition/BannonFaragePalmerAutomatedInfluenceReceiptsExact.agda").read_text()
    assert "Palmer.directContactPaid Palmer.bannonPalmerReceipt ≡ true" in s
    assert "Palmer.independentlyVerifiedInfluencePaid Palmer.bannonPalmerReceipt ≡ false" in s
    assert "EFTA01615861" in parent
    assert "one brief phone conversation" in parent
    assert "one brief unsolicited Bannon call" in d
    assert "initially denied all contact" in d
    assert "a call's exact time" in d.lower()
    assert "not" in d.lower()


def test_government_roles_are_not_collapsed_and_palmer_counterclaims_are_versioned():
    src = ADAPTER.read_text()
    assert "originalParliamentaryDeclaredInterest : AustraliaSourceRole" in src
    assert "originalElectoralRegulatorRule : AustraliaSourceRole" in src
    assert "sourceClaimAndDatedCounterStatement : AustraliaSourceRole" in src
    assert "hansonFloridaFlightsSenateDeclaration = australia-source-role-receipt\n  originalParliamentaryDeclaredInterest" in src
    assert "aecOldRegimeAnnualDisclosureGate = australia-source-role-receipt\n  originalElectoralRegulatorRule" in src
    assert "aecDisclosure2026PublicationOriginal = australia-source-role-receipt\n  originalElectoralRegulatorRule" in src
    assert "palmerRevisedContactAttribution = australia-source-role-receipt\n  sourceClaimAndDatedCounterStatement" in src
    assert "bannonPalmerContrarySourceReceipt = australia-source-role-receipt\n  sourceClaimAndDatedCounterStatement" in src
