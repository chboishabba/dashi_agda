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
        "hansonAircraftCorporateStatement = australia-source-role-receipt",
        "namedAssociatesOneNationCashSupport = australia-source-role-receipt",
        "hancockIPA2016And2017JudicialDocument = australia-source-role-receipt",
        "AUD 2.3m 2016 + AUD 2.2m 2017",
        "JUDGMENT reproduces",
        "bannonPalmerContrarySourceReceipt = australia-source-role-receipt",
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
    assert len(names) == 16
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
    ):
        assert mapping[k] == "true"
    for k in (
        "publishedDonorAnnualReturnSameAsReportedAprilDonation",
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
