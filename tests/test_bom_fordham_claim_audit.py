"""Static source-boundary regression for 2026-10 BOM/Fordham case.

This guards source/claim classifications, not climate-data computations, speaker
intent, the original Berger/Sherrington audit, or Agda kernel typechecking.
"""
from pathlib import Path
import csv
from collections import Counter

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda"
VALIDATION = ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditValidation.agda"
RESEARCH = ROOT / "docs/bom_fordham_temperature_claim_audit_20261024.md"


def test_existing_typed_genealogy_reused():
    text = OWNER.read_text()
    assert "import DASHI.Governance.TypedGenealogyEdgeExact as Typed" in text
    for edge, kind in [
        ("fordhamTo2GB", "Typed.personnelContinuity"),
        ("radioToTapt", "Typed.organisationalContinuity"),
        ("fordhamAuditBroadcast", "Typed.audienceAdjacency"),
    ]:
        assert edge in text and kind in text
    # No candidate is installed as a strong transfer evidence edge.
    assert "Typed.historicalTransfer Typed.primary" not in text
    assert "Typed.directMethodTransfer Typed.primary" not in text


def test_source_roots_preserve_chronology_and_not_obtained_audit():
    text = OWNER.read_text()
    assert "2026-10-19 AEST" in text
    assert "2026-10-22" in text
    assert "2026-05-01" in text
    assert "canonicalOriginalAuditStatus = notAcquired" in text
    assert "institutionHypothesised bomStatement" in text
    assert "allegationNotReproduced auditReporting" in text


def test_nonpromotion_regressions_and_bondi_distinction():
    code = OWNER.read_text()
    val = VALIDATION.read_text()
    docs = RESEARCH.read_text()
    required = [
        "duplicateDoesNotProveFraud",
        "rhetoricDoesNotProveBannonControl",
        "ownershipDoesNotProveEditorialOrder",
        "bondiCoverageDoesNotProveInflammatorySpeech",
        "fordhamTPUSA", "fordhamTPAU", "fordhamBannon",
    ]
    for name in required:
        assert name in code
    assert "noFraudPromotion" in val
    assert "noTPUSAPromotion" in val
    assert "2024 Bondi Junction" in docs
    assert "2025 Bondi Beach" in docs
    assert "1867 is pre-1910" in docs
    assert "postdates the episode" in docs


def test_bondi_media_and_false_hanson_attribution_are_separate_roots():
    owner = OWNER.read_text()
    docs = RESEARCH.read_text()
    for name in [
        "bondiFordhamPoliticalSegment",
        "fordhamLathamArchive",
        "aapBondiHansonFabrication",
        "tpaustFirstParty",
    ]:
        assert name in owner
    assert "fabricated quotes attributed to Pauline Hanson" in docs
    assert "not anti-Muslim words" in docs
    assert "Latham" in docs and "underlying allegation" not in owner


POLITICAL_OWNER = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Exact.agda"
POLITICAL_VALIDATION = ROOT / "DASHI/Governance/AustralianPoliticalRadioInfluence2026Validation.agda"


def test_direct_2026_ownership_and_revenue_do_not_collapse():
    body = POLITICAL_OWNER.read_text()
    docs = RESEARCH.read_text()
    for required in (
        "fordhamTapt",
        "kiisARN",
        "arnSandilandsRevenue",
        "arnNewsCorpExit",
        "19.9 percent",
        "ACMA records News Corp ceased",
        "2026-05-01",
    ):
        assert required in body or required in docs
    assert "noRevenueControlLeap" in body


def test_first_person_messaging_and_disputed_work_status():
    body = POLITICAL_OWNER.read_text()
    val = POLITICAL_VALIDATION.read_text()
    assert "kyleHansonMessaging" in body
    assert "namedActorSelfReport" in body
    assert "ashbyKyleQualification" in body
    assert "namedActorDenial" in body
    assert "noPaidCampaignPromotion" in val


def test_funding_event_attendance_and_climate_are_typed_distinct():
    body = POLITICAL_OWNER.read_text()
    for term in (
        "hancockAdvance",
        "advanceBannonAssociate",
        "harnwellBannon",
        "rinehartHansonPolicy",
        "plimerOneNation",
        "bannonPalmerCanonicalOwner",
        "acmaMpoxFinding",
        "acmaParalympicsFinding",
        "noFordhamCommandLeap",
    ):
        assert term in body
    assert "EFTA01615861" in body
    assert "palmerBannonConflict = relationship-receipt" not in body
    assert "noConferenceCommand" in POLITICAL_VALIDATION.read_text()


FRIENDLY = ROOT / "DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Exact.agda"
FRIENDLY_CHECKS = ROOT / "DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Validation.agda"


def test_single_owner_for_bannon_palmer_and_source_root():
    body = POLITICAL_OWNER.read_text()
    assert 'BannonFaragePalmerAutomatedInfluenceReceiptsExact' in body
    assert 'EFTA01615861' in body
    assert "palmerBannonConflict = relationship-receipt" not in body
    assert "bannonPalmerCanonicalOwner" in body


def test_new_show_legal_operator_and_investor_state():
    body = POLITICAL_OWNER.read_text()
    for token in (
        "newShowLegalOperator",
        "sandilandsSelfReportedOwnership",
        "aiimsProduction",
        "nineTaptStrategicPartnership",
        "kyleProposedARNBuyout",
        "Kyle Sandilands Live Pty Ltd",
        "ABN 24 699 610 261",
        "NET revenue",
        "thresholds/caps",
    ):
        assert token in body


def test_recent_friendlyjordies_independent_abc_findings():
    body = FRIENDLY.read_text()
    checks = FRIENDLY_CHECKS.read_text()
    for token in (
        "friendlyjordiesGovernanceWitness",
        "SensibLawFriendlyjordiesSourceTotalityExact",
        "breaking my silence",
        "2026-10-22",
        "2026-10-23",
        "Cocaine Nation",
        "Meth Highway",
        "abcOmbudsmansDetermination",
        "lamestreamCountercheck",
        "reportedWithDenial",
        "shanksHomeArsonNov2022",
        "bondiJunctionAttackApr2024",
        "bondiBeachAttackDec2025",
    ):
        assert token in body
    assert "editorialFailureNotCriminalThreat" in checks
    assert "screenshotProvenanceRequired" in checks


def test_arn_presenter_contractors_are_historical_equity_not_ksl_investors():
    body = POLITICAL_OWNER.read_text()
    vals = POLITICAL_VALIDATION.read_text()
    research = RESEARCH.read_text()
    for token in (
        "quasarARNHistoricalEquity",
        "hendersonARNHistoricalEquity",
        "quasarKyleService",
        "southernCrossARNIndirect",
        "stokesSouthernCrossStake",
        "3,161,166",
        "historicEquityHolding",
    ):
        assert token in body or token in research
    assert "newShowOperatorIsNotOwnership" in vals
    assert "proposedBuyoutIsNotCompleted" in vals
    assert "quasarServiceIsNotNewShowEquity" in vals
    assert "ACMA says News Corp Australia" in research


def test_direct_original_abc_ombudsman_five_findings_and_seven_actions():
    source = FRIENDLY.read_text()
    proofs = FRIENDLY_CHECKS.read_text()
    for token in (
        "ombudsmanOriginalExecutiveSummary",
        "39e8eeeffed7acde9a54d3ccc2f2a6fb",
        "finding1DoublePresentation",
        "finding2JasonVerification",
        "finding3SweeperApproval",
        "finding4BrendanContext",
        "finding5InstitutionalIntegrity",
        "canonicalFiveOmbudsmanFindings",
        "r1RemoveProgrammes",
        "r2BroaderInquiry",
        "r3PublishCorrection",
        "r4NamedAnonymityApprover",
        "r5LegalVersusEditorialRisk",
        "r6FactcheckAndUpwardReferral",
        "r7JuniorTeamSupport",
        "canonicalSevenOmbudsmanRecommendations",
        "institutionalAcceptanceDoesNotPayCompletion",
    ):
        assert token in source
    assert "acceptanceDoesNotVerifyCompletion" in proofs
    assert "findingFiveIsInstitutionalIntegrity" in proofs


def test_no_invented_ai_mode_claims_or_external_investors():
    documentation = RESEARCH.read_text()
    media = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    assert "https://share.google/aimode/Ux4UtsL535FOH9STw" in documentation
    # The original October 24 acquisition failure is now superseded by
    # the user-supplied transcript; its generated claims are not evidence.
    assert "SUPERSEDED by 25 October uploaded transcript" in documentation
    assert "Google AI Mode transcript acquired" in documentation
    assert "80b27d5b866a0a906142a6c66f3e090ad39342ecbe4173f088ef48ea61adbfcc" in documentation
    for receipt in (
        "kyleSubscriberFinanceSelfReport",
        "harveyNormanProspectiveSponsorship",
        "kyleUscreenPlatform",
    ):
        assert receipt in media
    assert "reportedSubscriptionsNotAudited" in media
    assert "advertiserOfferNotEquity" in media
    assert "subscriberFundingIsAttributedOnly" in checks
    assert "advertiserInterestNotCapitalStake" in checks


def test_google_ai_source_intake_reuses_political_radio_owner():
    """No source-specific Agda files for one AI-generated answer."""
    governance = ROOT / "DASHI/Governance"
    for obsolete in (
        "GoogleAIModeMediaClaimIntake2026Exact.agda",
        "GoogleAIModeMediaClaimIntake2026Validation.agda",
    ):
        assert not (governance / obsolete).exists()

    source = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    docs = RESEARCH.read_text()
    # Every retained relationship has a direct, source-graded owner here;
    # other speculative leads stay only in the narrative evidence ledger.
    for receipt in (
        "rinehartBannonDevineEvent",
        "advanceSheahanBannonConversation",
        "rinehartMcWilliamSecuredMediaStake",
        "rinehartStefanovicPodcastFundingClaim",
        "stefanovicRobinsonPublication",
        "hansonRepublishedRobinson",
        "mandelsonXstrataEpsteinTaxEmail",
        "jonesGillardRecordedRemark",
        "rinehartOneNationHeadOffice",
        "stefanovicIbrahimOwnershipSettlement",
        "mfwKyleAdvertiserCampaign",
    ):
        assert source.count(receipt + " : RelationshipReceipt") == 1

    for proof in (
        "rinehartStakeIsSecuredFinancing",
        "stefanovicFundingRemainsReported",
        "hansonRepostIsRedistribution",
        "sheahanChatRemainsReported",
        "taxEvidenceIsCorrespondence",
        "headquartersIsReportedLease",
        "podcastBuyoutNotRinehartEquity",
        "MFWPressureIsAdvertiserCampaign",
    ):
        assert proof in checks

    assert "PR #1131" in docs
    assert "not its own mathematical owner" in docs
    assert "DASHI.Governance.GoogleAIModeMediaClaimIntake2026" not in source + checks


def test_cross_pollination_reuses_woogaroo_climate_and_project2025_owners():
    """A bounded effect question isn't a new claim of gas lobbying or US direction."""
    political = POLITICAL_OWNER.read_text()
    docs = RESEARCH.read_text()
    for token in (
        "independentOriginalClaimConcentration",
        "donorAdjacentGasPolicyShift",
        "project2025PolicyProposalVersusEnactment",
        "springfieldResidentialGasDemandPersistence",
    ):
        assert token in political

    for source_owner in (
        "SensibLawSpringfieldGasLobbyingOwnershipSnowballExact",
        "SensibLawAzureSpringfieldInducedGasDemandExact",
        "HansonCapacityCriticismHyperformalismExact",
        "ClimateGenealogyTypedCasesExact",
        "GodsEyeViewWorldEpistemicSourceAtlasExact",
        "GodsEyeViewDiagnosisDrivenActivistRollupExact",
    ):
        assert source_owner in docs

    for bounded_claim in (
        "10.1177/09636625231202117",
        "10.1038/s41598-021-01714-4",
        "8,000 gas connections",
        "Bernard L. McNamee",
        "Mandy M. Gunasekara",
        "same-object",
        "N_eff",
        "Senex 8 May 2026",
        "One Nation 9 June 2026",
    ):
        assert bounded_claim in docs

    # No duplicated named company/donation source receipts are placed into
    # the media file, and no unsupported lobbying→appliance causal edge exists.
    assert "azureLnpDonation2019A = attributed-influence-edge" not in political
    assert "springfieldRegisteredLobbyistMeeting2025 = attributed-influence-edge" not in political
    assert "actual same-object policy-to-asset-to-household" not in political


ORIGIN_EDGE_LEDGER = ROOT / "Docs/support/reference/australian_climate_claim_origin_edges_20261025.csv"


def test_original_claim_edges_are_source_qualified_and_do_not_invent_transfers():
    """Machine-check source families, chronology and non-causality boundaries."""
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))

    assert len(rows) == 25
    assert len({row["edge_id"] for row in rows}) == len(rows)
    assert Counter(row["case_id"] for row in rows) == {
        "BOM2026": 11, "REEF2021": 10, "GAS2026": 4
    }
    fields = (
        "edge_id", "case_id", "upstream", "downstream", "relation",
        "evidence_grade", "date_local_or_month", "locator", "boundary"
    )
    assert all(all(row.get(field) for field in fields) for row in rows)
    assert all(row["locator"].startswith("https://") for row in rows)
    assert all(len(row["boundary"]) >= 40 for row in rows)

    # Reported interpretations are not the original science.
    reef_opinion = next(row for row in rows if row["edge_id"] == "R03")
    assert reef_opinion["relation"] == "named_alternative_interpretation"
    assert "not AIMS conclusion" in reef_opinion["boundary"]

    # An FOI-supported leak is real while Ridd's opinion commission is not proven.
    selected_media = next(row for row in rows if row["edge_id"] == "R02")
    assert selected_media["evidence_grade"] == "foi_reported_by_abc"
    assert "distinct from Ridd" in selected_media["boundary"]

    # ACMA specific 2023 determinations do not adjudicate entire Sky network.
    acma = next(row for row in rows if row["edge_id"] == "R07")
    assert acma["evidence_grade"] == "acma_determination"
    assert "not all Sky" in acma["boundary"]

    # The May primary policy statement precedes the June party policy. Their
    # similarity is not documentary proof of transmission or a payment.
    gas = next(row for row in rows if row["edge_id"] == "G01")
    assert gas["relation"] == "argument_overlap_not_copy_proof"
    assert gas["evidence_grade"] == "two_independent_primary_texts"
    assert "2026-05-08/2026-06-09" in gas["date_local_or_month"]
    assert "no proved" in gas["boundary"]

    # Claims of provenance are not evidence just because many republications
    # share the same origin; explicitly mark secondary byline propagation.
    publications = [
        row for row in rows if row["relation"] in {
            "credited_guest_publication",
            "explicit_author_republication",
            "explicitly_credited_reporting",
            "credited_crosspublication",
        }
    ]
    assert len(publications) >= 5
    assert all(
        row["evidence_grade"] in {
            "same_author_content", "named_original_reporter"
        } for row in publications
    )


def test_claim_root_ledger_documentation_uses_only_case_bounded_counts():
    docs = RESEARCH.read_text()
    assert "australian_climate_claim_origin_edges_20261025.csv" in docs
    assert "25 bounded relationship rows" in docs
    assert "NOT a representative crawl" in docs
    assert "originator" in docs.lower()
    assert "actual transfer not established" in docs.lower()


def test_directed_release_and_original_claim_amplification_are_not_collapsed():
    media = POLITICAL_OWNER.read_text()
    checks = POLITICAL_VALIDATION.read_text()
    for original, kind in (
        ("leyAimsTargetedMediaPreview", "timedTargetedInformationRelease"),
        ("riddIndependentReefOpinion", "originalOpinionProduction"),
        ("mooreAmplifiedRiddReefClaim", "traceableClaimAmplification"),
        ("acmaReefOutsidersFinding", "enforcementFinding"),
    ):
        assert media.count(original + " : RelationshipReceipt") == 1
        assert kind in media

    for token in (
        "reefReleaseIsTimedMediaAccess",
        "riddOpinionNotAimsMeasurement",
        "mooreRepostNotIndependentMeasurement",
        "reefRegulatoryFindingIsSpecific",
        "reefReleaseNotMinistryEditorialControl",
        "riddDistributionNotCoordinatedCommand",
    ):
        assert token in checks
    assert "BI-645, BI-646, BI-647" in media
    assert "not proof" in media.lower()


def test_original_bom_clips_and_historical_ipa_finance_use_different_types():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        by_id = {row["edge_id"]: row for row in csv.DictReader(stream)}

    assert by_id["B10"]["relation"] == "direct_clip_reuse_in_transcript"
    assert by_id["B11"]["relation"] == "hosted_interview_republication"
    assert by_id["B10"]["downstream"].startswith("Sky News Outsiders")
    assert by_id["R09"]["evidence_grade"] == "ipa_first_party_press_release"
    assert by_id["R10"]["relation"] == "historical_institutional_donation"
    assert "not payment to Ridd or Sky" in by_id["R10"]["boundary"]

    docs = RESEARCH.read_text()
    assert "Peter Ridd on Outsiders News24" in docs
    assert "Hancock Prospecting" in docs
    assert "no same-object payment" in docs
    assert "Fordham's production" in docs
