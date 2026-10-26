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
        "oneNationUnlimitedPensionerPolicyEnactedInLawVerified",
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


def test_february_2022_bill_is_not_august_2022_lobbying():
    """Official docket identity is not proof of a financial or causal handoff."""
    s = ADAPTER.read_text()
    assert "coalitionFeb2022BillDocket = australia-source-role-receipt" in s
    assert "2022-02-10" in s
    assert "senateSeptember2022MultipleSubmitterDocket = australia-source-role-receipt" in s
    assert "HPPL #3" in s and "IPA #6" in s and "National Seniors #7" in s
    assert "accciDecember2021IndependentAlternative = australia-source-role-receipt" in s
    assert "act55OfficialStatute = australia-source-role-receipt" in s
    assert "2022-11-23" in s
    assert "februaryBillIsNotAugustSubmission :" in s
    assert "februaryBillIsNotAugustSubmission ()" in s
    assert "enactedLimitedActIsNotUnlimitedPartyPledge ()" in s
    assert "Underlying PDF page bytes not inspected" in s
    assert "not an observed employment increase" in s


def test_official_stages_have_distinct_declared_constructors_and_institutional_producers():
    s = ADAPTER.read_text()
    a = s.index("data PensionLegislativeObject : Set where")
    b = s.index("data DistinctObject : Set where", a)
    constructors = re.findall(r"^  ([A-Za-z][A-Za-z0-9]*) : PensionLegislativeObject$", s[a:b], re.M)
    assert constructors == [
        "feb2022CoalitionBill",
        "august2022SenateSubmissions",
        "nov2022Act55",
        "jan2025OneNationPledge",
    ]
    for receipt in (
        "coalitionFeb2022BillDocket",
        "senateSeptember2022MultipleSubmitterDocket",
        "accciDecember2021IndependentAlternative",
    ):
        assert receipt + " = australia-source-role-receipt\n  governmentIndexedAdvocacySubmission" in s
    assert ("act55OfficialStatute = australia-source-role-receipt\n"
            "  originalLimitedGovernmentLegislation") in s
    assert "a submission does not by itself establish bill drafting influence" in s.lower()


def test_three_inquiries_not_one_submitter_register():
    """Three official registers, seven specifically typed source appearances."""
    s = ADAPTER.read_text()
    for key in (
        "februaryCoalitionSenateRegisterOriginal",
        "augustDeanSmithBillOriginal",
        "septemberAlbaneseBillOriginal",
        "octoberGovernmentSenateRegisterOriginal",
        "hancockOct2022OwnSubmissionIndexReceipt",
        "df5522d8-50d8-4ebb-ad5d-6d7cfd367158",
        "dfaa59de-73b8-4409-ab06-4527c2c6cfd3",
        "8f9cfa11-5287-40b3-8287-4fbff1f88b80",
        "7596775e-a631-40bd-be57-abe6b5efd5a1",
        "85a023f4-e99a-45b0-8cf7-785af6302d45",
        "146b77ac-abc8-42c9-a937-8f5a45b40c3f",
        "febAndAugCommitteesAreDifferent ()",
        "augAndOctCommitteesAreDifferent ()",
        "sameNsaCannotYieldUniqueCommittee choose feb aug =",
        "noListedHancockFebSubmission ()",
    ):
        assert key in s
    block = s[s.index("data Pension2022IndexedSubmission :"):
              s.index("febAndAugCommitteesAreDifferent :")]
    registered = re.findall(r"^\s+(nsaFeb03|hancockAug03|ipaAug06|nsaAug07|nsaOct03|hancockOct09|ipaOct10) :", block, re.M)
    assert len(registered) == 7 and len(set(registered)) == 7
    assert "NO HPPL or IPA among SIX listed submissions" in s
    assert "this is only bounded absence" in s
    assert "Original PDF faces not inspected" in s


def test_nsa_ipa_original_survey_citation_is_not_hancock_editorial_order():
    s = ADAPTER.read_text()
    for marker in (
        "senateOct22IPACitesNSASurvey = australia-source-role-receipt",
        "senate2022MultipleDistinctPolicyAmounts = australia-source-role-receipt",
        "paragraphs 2.15-2.16",
        "National Seniors survey",
        "20% pensioner participation",
        "ACCI 15600",
        "VCCI extra 10000",
        "NSA 6000 biannual",
        "documentedNSAtoIPACitation = publicThirdPartySurveyCitation",
        "documentedNSAtoDeloitteModelling = namedClientConsultantCommission",
        "noCitationEqualsPrivateSponsorEditorialOrder ()",
        "No HPPL commissioning",
    ):
        assert marker in s
    assert s.index("senateOct22IPACitesNSASurvey") < s.index(
        "noCitationEqualsPrivateSponsorEditorialOrder")
    assert "Original public committee ANALYSIS" in s
