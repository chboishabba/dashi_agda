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

    assert len(rows) == 54
    assert len({row["edge_id"] for row in rows}) == len(rows)
    assert Counter(row["case_id"] for row in rows) == {
        "BOM2026": 24, "REEF2021": 10, "GAS2026": 20
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
    assert "54 bounded relationship rows" in docs
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


def test_single_bom_sky_clip_ipa_publication_and_old_donor_not_collapsed():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    for name in (
        "skyOutsidersLloydRiddSameProgramme",
        "ipaHostsBOMOutsidersTranscript",
        "ipaRiddResearchFellowship",
        "hancockToIPAHistoricalFunding",
    ):
        assert media.count(name + " : RelationshipReceipt") == 1

    for name in (
        "outsidersLloydRiddSameProgrammeIsPublished",
        "ipaOwnTranscriptIsDerivativePublication",
        "riddFellowshipIsNamedInstitutionalRelation",
        "historicHancockIPAIsNotCurrentEarmarkedPayment",
        "historicalIPAReceiptNotEditorialOrder",
        "publishedBOMInterviewNotSecretCommand",
    ):
        assert name in validation

    assert "historicalInstitutionalFunding" in media
    assert "4.5m" in media
    assert "no same-object payment" in RESEARCH.read_text()


def test_international_republication_is_not_fresh_climate_evidence():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        entries = {r["edge_id"]: r for r in csv.DictReader(stream)}
    assert entries["B12"]["relation"] == "explicit_international_translation"
    assert entries["B12"]["evidence_grade"] == "first_party_translation_credit"
    assert entries["B13"]["relation"] == "news_digest_reference"
    assert entries["B13"]["evidence_grade"] == "named_source_linking"
    assert "No independent BOM ledger verification" in entries["B12"]["boundary"]
    assert "not independent audits" in RESEARCH.read_text()


def test_canonical_origin_keys_do_not_miscount_common_republication():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 54
    assert all(row["root_key"] and row["root_resolution"] for row in rows)
    by_id = {row["edge_id"]: row for row in rows}
    assert by_id["G05"]["root_key"] == by_id["G06"]["root_key"] == "G_CREIGHTON_OPINION"
    assert by_id["G07"]["root_key"] == by_id["G08"]["root_key"] == "G_JOHNSON_REPORT"
    assert by_id["B03"]["root_key"] == by_id["B12"]["root_key"] == "B_NOVA_COMMENTARY"
    assert by_id["G01"]["root_key"] == "MULTI"
    assert by_id["G09"]["root_key"] == "MULTI"
    assert by_id["G10"]["root_key"] == "MULTI"
    assert by_id["G13"]["root_key"] == "MULTI"
    # The 31 source/template family labels are manually assigned within this purposive case
    # graph, not a statistic of Australian media or distinct truth sources.
    labeled = {r["root_key"] for r in rows if r["root_key"] != "MULTI"}
    assert len(labeled) == 31
    assert sum(r["root_key"] == "MULTI" for r in rows) == 9


def test_senex_hancock_ipa_information_path_has_explicit_public_countercase():
    media = POLITICAL_OWNER.read_text()
    proofs = POLITICAL_VALIDATION.read_text()
    doc = RESEARCH.read_text()
    for receipt in (
        "creightonIPAOriginalArticle",
        "senexLinksIPACreighton",
        "hancockReprintsJohnsonNightly",
        "senexLinksJohnsonNightly",
        "senateGasTaxInquiryPublicComparator",
    ):
        assert media.count(receipt + " : RelationshipReceipt") == 1
    for witness in (
        "creightonOriginalCreditIsAttributedReuse",
        "gasProducerLinksIPAOriginal",
        "hancockSameJournalismNotIndependentData",
        "senexSameJournalismNotIndependentData",
        "parliamentaryPublicPolicyCounterexample",
        "gasRepublishingDoesNotEstablishPolicyCopy",
        "politicalLanguageDoesNotEstablishCommonSponsor",
    ):
        assert witness in proofs
    assert "No new Agda ontology" in doc
    assert "Stephen Johnson" in doc and "Adam Creighton" in doc
    assert "230+ submissions" in doc
    assert "31 selected source/template family labels" in doc


def test_one_nation_gas_policy_is_not_dated_before_public_inquiry():
    doc = RESEARCH.read_text()
    assert "Senate committee **7 May** report" in doc
    assert "One Nation's **9 June**" in doc
    assert "7 May precedes 8 May" in doc
    assert "actual transfer not established" in doc.lower()


def test_two_independent_political_frames_inside_single_sky_interview():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    documentation = RESEARCH.read_text()
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        keyed = {r["edge_id"]: r for r in csv.DictReader(stream)}

    assert keyed["B14"]["root_key"] == "B_RIDD_2026_INTERVIEW"
    assert keyed["B15"]["root_key"] == "B_DEAN_2026_SHOW_FRAME"
    assert keyed["B14"]["root_key"] != keyed["B15"]["root_key"]
    assert "not verified" in keyed["B14"]["boundary"]
    for name in ("riddBOMGasLitigationArgument", "rowanDeanBOMNetZeroArgument"):
        assert media.count(name + " : RelationshipReceipt") == 1
    for name in ("riddCrossDomainIsAttributedArgument", "deanClimatePolicyIsAttributedArgument",
                 "riddClaimDoesNotProveGasLitigationCausality", "deanClaimDoesNotProvePoliticalCoordination"):
        assert name in validation
    assert "unspecified Western Australian gas project" in documentation
    assert "31 selected source/template family labels" in documentation


def test_browse_epbc_primary_request_cannot_promote_expert_claim_to_decision():
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    docs = RESEARCH.read_text()
    for named in (
        "browseACFOriginalS78AApplication",
        "browse2026ValidityDecisionOnly",
        "browseCitedAbramScienceMethod",
        "perkinsKirkpatrickBrowseExpertModel",
        "riddSpecificBrowseReferentInference",
        "fordhamOriginalFourMinutePodcastCarrier",
    ):
        assert media.count(named + " : RelationshipReceipt") == 1
    for proof in (
        "browseRequestIsNotCourtJudgment",
        "validityOnlyNotFinalDecision",
        "abramMethodPrecedesSpecificBrowseEstimate",
        "specificExpertModelNotMeasurement",
        "unnamedRiddGasReferentIsInferred",
        "fourMinuteAudioLocatorNotTranscript",
        "epbcProceduralStatusDoesNotProveMerits",
        "fourMinutePodcastLocatorDoesNotProveWords",
        "similarNumDoesNotProveSourceConsulted",
    ):
        assert proof in validation
    assert "2018/8319" in media and docs
    assert "29.35" in media and docs
    assert "10.1038/s44168-025-00296-5" in media and docs
    assert "not a substantive merits decision" in docs.lower()
    assert "Annexure A" in media


def test_fordham_publication_time_and_browse_original_root_split():
    import datetime
    from zoneinfo import ZoneInfo

    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        items = {row["edge_id"]: row for row in csv.DictReader(stream)}
    assert len(items) == 54
    assert items["B16"]["root_key"] == "MULTI"
    assert items["B21"]["root_key"] == "MULTI"
    assert items["G14"]["root_key"] == "MULTI"
    assert items["B17"]["root_key"] == "B_ACF_BROWSE_REQUEST"
    assert items["B18"]["root_key"] == "B_ABRAM_2025_METHOD"
    assert items["B19"]["root_key"] == "B_PERKINS_BROWSE_EXPERT"
    assert items["B20"]["root_key"] == "B_FORDHAM_AUDIO"
    assert items["B20"]["root_resolution"] == "native_publication_identity_no_spoken_quote"

    utc = datetime.datetime(2026, 10, 18, 21, 55, tzinfo=datetime.timezone.utc)
    brisbane = utc.astimezone(ZoneInfo("Australia/Brisbane"))
    assert (brisbane.year, brisbane.month, brisbane.day, brisbane.hour, brisbane.minute) == (2026, 10, 19, 7, 55)

    docs = RESEARCH.read_text()
    assert "54 evidence edges" in docs  # current sample after acquisition
    assert "not a court lawsuit" in docs
    assert "not a court lawsuit" in docs and "not a substantive merits decision" in docs.lower()


def test_gas_committee_five_form_letters_are_template_counts_not_five_authors():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        rows = {row["edge_id"]: row for row in csv.DictReader(stream)}
    templates = {"G15":272, "G16":13, "G17":52, "G18":15, "G19":14}
    assert sum(templates.values()) == 366
    for ref, count in templates.items():
        row = rows[ref]
        assert row["relation"] == "documented_form_letter_template_repeat"
        assert row["evidence_grade"] == "senate_committee_primary_report_paragraph_1_6"
        assert str(count) in row["downstream"]
        assert row["root_key"].startswith("G_TEMPLATE_")
    # Three template creators are explicitly unknown; a technology platform
    # is not established as the author of the campaign text it transmitted.
    for ref in ("G15", "G18", "G19"):
        assert rows[ref]["root_resolution"] == "committee_template_identity_author_unknown"
    assert rows["G17"]["root_resolution"] == "platform_route_not_original_text_author"
    assert rows["G20"]["root_key"] == "G_GETUP_PETITION"
    assert "50000" in rows["G20"]["downstream"]
    assert "not 50000 independent" in rows["G20"]["boundary"]

    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    for name in ("gasTaxSenateFiveTemplateFamilies", "gasTaxGetUpPetitionAggregate"):
        assert media.count(name + " : RelationshipReceipt") == 1
    for proof in (
        "gasTemplateFamiliesAreDistinctFromIndependentModels",
        "getupPetitionCountsSupportNotIndependentModels",
        "noConspiracyFromTemplateCounts",
    ):
        assert proof in validation


def test_bom_report_custody_is_not_access_to_original_audit():
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        item = {r["edge_id"]:r for r in csv.DictReader(stream)}["B22"]
    assert item["root_key"] == "B_AUDIT_ATR"
    assert item["relation"] == "reported_private_copy_and_permission_constraint"
    assert "not released or inspected" in item["boundary"]
    media = POLITICAL_OWNER.read_text()
    validation = POLITICAL_VALIDATION.read_text()
    assert media.count("novaClaimsFullBOMAuditCopy : RelationshipReceipt") == 1
    assert "unpublishedAuditPossessionNotSourceInspection" in validation
    assert "noProvenAuditFromPersonalCustodyReport" in validation


def test_browse_central_estimate_exact_rational_consistency_only():
    """Checks conditional arithmetic, NOT ecological validity or uncertainty."""
    from fractions import Fraction as Q
    browse_emissions_mt = Q("1597.41")
    tcre_c_per_million_mt = Q("0.45") / 1_000_000
    gbr_dhw_per_c = Q("4.4")
    cover_fraction_per_dhw = Q("0.035")
    hectares = 1_060_000
    colonies_per_hectare = 250_000

    warming = browse_emissions_mt * tcre_c_per_million_mt
    dhw = warming * gbr_dhw_per_c
    cover_loss_fraction = dhw * cover_fraction_per_dhw
    estimated_colonies = cover_loss_fraction * hectares * colonies_per_hectare
    assert warming == Q(1437669, 2000000000)
    assert estimated_colonies == Q(5867127189, 200)  # 29,335,635.945
    assert abs(estimated_colonies - 29_350_000) / 29_350_000 < Q(1, 2000)

    # The paper's independently described Scarborough example (~16m)
    # uses the same method but a *different project emissions input*.
    scarborough = Q(876) * tcre_c_per_million_mt * gbr_dhw_per_c * cover_fraction_per_dhw * hectares * colonies_per_hectare
    assert scarborough == 16_087_302

    docs = RESEARCH.read_text()
    assert "29,335,635.945" in docs
    assert "16,087,302" in docs
    assert "kernel-verified Agda theorem" in docs


def test_finite_agda_template_and_browse_arithmetic_witnesses_declared():
    """Declaration and source checks only; this is NOT a kernel typecheck."""
    proofs = POLITICAL_VALIDATION.read_text()
    assert "open import Agda.Builtin.Nat using (_+_; _*_)" in proofs
    assert "gasCommitteeOriginalTemplateTotals" in proofs
    assert "272 + 13 + 52 + 15 + 14 ≡ 366" in proofs
    assert "browseConditionalModelNumeratorExact" in proofs
    assert "159741 * 45 * 44 * 35 * 1060000 * 250000" in proofs
    assert "2933563594500000000000" in proofs
    assert "browseConditionalModelScaleExact" in proofs
    assert "5867127189 * 500000000000" in proofs
    assert "does not make them" in proofs


def test_readfearn_precision_countercheck_and_annex_index_are_distinct_sources():
    """An independent news analysis is not an instrument log; an index is not a PDF."""
    with ORIGIN_EDGE_LEDGER.open(newline="", encoding="utf-8") as stream:
        entries = {r["edge_id"]: r for r in csv.DictReader(stream)}
    assert entries["B23"]["root_key"] == "B_READFEARN_METHOD_CHECK"
    assert entries["B23"]["relation"] == "journalistic_adversarial_primary_method_query"
    assert entries["B23"]["evidence_grade"] == "named_journalist_original_report"
    assert "not independent 2004 temperature measurement" in entries["B23"]["boundary"]
    assert entries["B24"]["root_key"] == "B_PERKINS_BROWSE_EXPERT"
    assert entries["B24"]["root_resolution"] == "original_pdf_listed_retrieval_unpaid"
    assert "uninspected" in entries["B24"]["boundary"]

    original = (ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/BOMFordhamMediaClaimAuditValidation.agda").read_text()
    sensitivity = (ROOT / "tests/test_bom_climate_sensitivity_bounds.py").read_text()
    for token in (
        "readfearnPalmervillePrecisionCheck",
        "palmervillePrecisionLossWitness",
        "INF.NonFactorabilityWitness",
        "palmervilleRoundedValuesCannotDetermineUnroundedDayOne",
        "palmervilleDifferentUnderlyingValue",
    ):
        assert token in original
    for token in (
        "palmervilleDistinctHistoriesSameSeventeenRoundedObservations",
        "palmervilleDifferentLatentDayOneIsNotRecoverable",
        "palmervilleMeasurementPrecisionNotAProbability",
        "INF.FactorsThrough",
    ):
        assert token in validation
    assert "test_seventeen_identical_rounded_days_do_not_identify_latent_tenths" in sensitivity
    assert "test_integer_precision_preserves_a_nontrivial_degree_bin" in sensitivity

    docs = RESEARCH.read_text()
    assert "The two constructed histories are illustrative" in docs
    assert "source-content gap" in docs
    assert "706 KB" in docs
    assert "31 manually curated root-or-template labels" in docs


def test_climate_origins_same_api_plan_and_actual_people_not_url_multiplicity():
    """Independent plan authorship and named people are not 13 independent scientific papers."""
    import re
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    manifest = ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv"
    with manifest.open(newline="", encoding="utf-8") as src:
        records = list(csv.DictReader(src))
    assert len(records) == 41
    ids = [r["edge_id"] for r in records]
    assert len(ids) == len(set(ids))
    contributed = [r for r in records if re.fullmatch(r"E8-\d\d", r["edge_id"])]
    assert len(contributed) == 13
    assert all(r["evidence_strength"] == "A_primary" for r in contributed)
    assert all("US Congressional Record 27 Apr 1998" in r["source_citation"] for r in contributed)
    assert all("not" in r["notes"].lower() for r in contributed)
    assert len(re.findall(r"^apiNamedContributor\w+ : Typed.TypedGenealogyEdge$", climate, re.MULTILINE)) == 13
    assert "allAPIContributorsInExampleShareOneOriginalDocument" in validation

    by_id = {r["edge_id"]: r for r in records}
    assert by_id["E9-08"]["relation_kind"] == "funding"
    assert by_id["E9-08"]["evidence_strength"] == "A_primary"
    assert by_id["E9-09"]["relation_kind"] == "organizational_continuity"
    assert by_id["E9-10"]["relation_kind"] == "personnel_continuity"
    assert by_id["E9-11"]["relation_kind"] == "personnel_continuity"
    assert "Steve Milloy" in by_id["E9-11"]["from_node"]

    for item in (
        "exxonInternal1982", "shellInternal1988", "gccLennyBernstein1995",
        "shellFirstParty1998", "bpLeadership1997",
        "mooreCO2Coalition", "mooreHeartland", "greenpeaceHistory",
        "hancockIPAJudgment", "brulleFoundationStudy",
        "farrellNetworkStudy", "supranRahmstorfOreskesExxonAudit",
        "milloy1998ToReefMedia",
    ):
        assert item in climate
    for caution in (
        "apiContributorNotMethodTransfer", "ipaFundingNotEditorialMethod",
        "cfactContinuationNotPlanTransfer", "milloyRepeatNotProofOfTwentyThreeYearPlan",
    ):
        assert caution in climate

    docs = RESEARCH.read_text()
    assert "26 October 2026 — funded climate countermovement originators" in docs
    assert "900m amount includes all activities" in docs.lower() or (
        "900m amount includes all activities" in climate.lower()
    ) or "900m amount includes all activities" in docs.lower()
    assert "41 rows" in docs
    assert "same-NAMED-PERSON continuity" in docs


def test_climate_original_claim_proofs_do_not_promote_funding_to_edits():
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    val = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    for item in (
        "apiPlanParticipationCannotBecomeMethodTransmission",
        "hancockIPAFundingCannotBecomeAutomaticMessageControl",
        "cfact1998And2026DoNotAutomaticallyProveContinuousPlan",
        "milloy1998To2021IsPersonnelNotScriptTransmission",
        "repeatPersonDoesNotProveOriginalAPIPlanStillActive",
        "foundationIncomeNotSameAsClimateDenialExpenditure",
        "industryDefectionsNotErased",
    ):
        assert item in val
    assert "typedGenealogyEdge" in climate
    assert "false false false" not in climate  # not a new political-radio triple system


def test_original_ice_and_singer_budget_states_do_not_invent_payment():
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    with (ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv").open(
        newline="", encoding="utf-8"
    ) as fd:
        cases = {r["edge_id"]: r for r in csv.DictReader(fd)}
    assert len(cases) == 41
    assert cases["E9-12"]["relation_kind"] == "organizational_continuity"
    assert cases["E9-13"]["relation_kind"] == "funding_commitment"
    assert cases["E9-14"]["relation_kind"] == "organizational_continuity"
    assert cases["E9-15"]["relation_kind"] == "funding_proposal"
    assert cases["E9-13"]["evidence_strength"] == "B_corroborated"
    assert cases["E9-15"]["evidence_strength"] == "B_corroborated"
    assert "payment transaction not independently inspected" in cases["E9-13"]["notes"]
    assert "not evidence it was disbursed" in cases["E9-15"]["notes"]

    for exact in ("fundingProposal : RelationKind", "fundingCommitment : RelationKind",
                  "fundingProposalIsNotTransferRelation", "fundingCommitmentIsNotTransferRelation"):
        assert exact in typed
    for item in ("ice1991TestCampaign", "singerGCC1994Proposal",
                 "southernCompany1991To1998", "southernICEPledgeNotDisbursement",
                 "singer1994ToSEPP1998", "singerGCCSolicitationNotMoneyPaid"):
        assert item in climate
    for item in ("singerGCCBudgetIsRequestNotPaidGrant",
                 "southernICEBudgetIsCommitmentNotBankTransfer",
                 "singer1994ProposalCannotEstablishMethodTransfer",
                 "southern1991PledgeCannotEstablishMethodTransfer"):
        assert item in validation
    doc = RESEARCH.read_text()
    assert "41 evidence edges" in doc
    assert "Singer → tobacco funders" in doc
    assert "this audit has **not acquired a specific dated BP internal technical memo" in doc


def test_gcc_acsh_commission_editorial_rights_and_published_file_are_distinct():
    """CIC documented contract/editorial authority is not proof of exact 1997 text identity."""
    import re
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    climate = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    validation = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    with (ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        cases = {row["edge_id"]: row for row in csv.DictReader(handle)}
    assert len(cases) == 41

    expected = {
        "E9-16": "commissioned_research",
        "E9-17": "editorial_review_rights",
        "E9-18": "topical_publication_match",
        "E9-19": "funding",
    }
    for id_, rel in expected.items():
        assert cases[id_]["relation_kind"] == rel
        assert cases[id_]["evidence_strength"] == "B_corroborated"
    assert "not proof" in cases["E9-18"]["notes"].lower() or "unproven" in cases["E9-18"]["notes"].lower()
    assert "not" in cases["E9-17"]["notes"].lower()
    assert "USD2774000" in cases["E9-19"]["notes"]

    for relation in ("commissionedResearch", "editorialReviewRights", "topicalPublicationMatch"):
        assert relation + " : RelationKind" in typed
    for named in (
        "gccACSHCommissionedClimateHealth", "gccACSHDocumentedEditorialReviewRights",
        "gccACSH1997PublicPaperMatch", "exxonToCHCReportedPostAPIGrants",
        "gccACSHSharedSubjectNotIdenticalFinalFile",
        "gccACSHContractualRightsNotProofOfSpecificScientificEdit",
    ):
        assert named in climate
    for named in (
        "gccACSHResearchWasCommissionedAccordingToArchive",
        "gccACSHClientReviewRightsNotProofOfActualEditing",
        "gccACSHPublishedSubjectOverlapNotSameFile",
        "exxonLaterCHCFundingIsBoundedHistoricalReporting",
        "acshTopicalMatchCannotProveTransfer",
        "acshEditorialDiscretionDoesNotProveSpecificScientificEdit",
        "singerGCCProposalUnacquiredDocumentIsCorroborated",
    ):
        assert named in validation

    assert "Typed.fundingProposal Typed.corroborated" in climate
    assert cases["E9-15"]["evidence_strength"] == "B_corroborated"
    assert "subsequently disputed" in cases["E8-02"]["notes"]
    assert re.search(r"apiNamedContributorCandaceCrandall : Typed.TypedGenealogyEdge", climate)
    docs = RESEARCH.read_text()
    assert "41 evidence edges" in docs
    assert "DocumentCloud page retrieval failed" in docs
    assert "no evidence the USD73,000 was ever paid" in docs


def test_climate_historical_object_identity_and_access_are_not_speaker_counts():
    """13 listed API people share one primary planning object, not 13 studies."""
    import re
    path = ROOT / "Docs/support/reference/climate_genealogy_typed_edges.csv"
    with path.open(newline="", encoding="utf-8") as fd:
        rows = list(csv.DictReader(fd))
    assert len(rows) == 41
    assert all(row["evidence_object_ids"] and row["acquisition_scope"] for row in rows)
    by_id = {row["edge_id"]: row for row in rows}
    participants = [r for r in rows if re.fullmatch(r"E8-\d\d", r["edge_id"])]
    assert len(participants) == 13
    assert {r["evidence_object_ids"] for r in participants} == {"API_PLAN_1998"}
    assert {r["acquisition_scope"] for r in participants} == {"primary_draft_listed_contributor"}
    assert by_id["E3"]["evidence_object_ids"] == "API_PLAN_1998"
    # A quoted report can support a relation without providing a private file
    # or even one identifiable primary object for an unresolved transfer.
    assert by_id["E6"]["evidence_object_ids"] == "UNRESOLVED"
    assert by_id["E7"]["evidence_object_ids"] == "UNRESOLVED"
    assert by_id["E4"]["evidence_object_ids"] == "BW_1969|API_PLAN_1998"
    assert by_id["E4b"]["evidence_object_ids"] == "BW_1969|API_PLAN_1998"
    assert by_id["E9-08"]["acquisition_scope"] == "court_judgment_reproduced_excerpt"
    assert by_id["E9-15"]["acquisition_scope"] == "proposal_original_unread"
    assert by_id["E9-16"]["acquisition_scope"] == "archive_index_contract_unread"
    assert by_id["E9-17"]["acquisition_scope"] == "archive_index_rights_unread"

    # The ACSH publisher's ORIGINAL 1997 text is now inspectable. The
    # original GCC client contract and final edited manuscript still are not.
    acsh = by_id["E9-18"]
    assert "ACSH_OFFICIAL_ARTICLE_1997" in acsh["evidence_object_ids"]
    assert "GCC_ACSH_GRANT_1996_INDEX" in acsh["evidence_object_ids"]
    assert "original_text_inspected" in acsh["acquisition_scope"]
    assert "final_equivalence_unresolved" in acsh["acquisition_scope"]
    assert "acsh.org/news/1997/10/01/global-climate-change-and-human-health" in acsh["source_citation"]

    brief = by_id["E9-20"]
    assert brief["relation_kind"] == "recommendation_exposure"
    assert brief["evidence_strength"] == "B_corroborated"
    assert "STATE_2001_BRIEFING_UNACQUIRED" in brief["evidence_object_ids"]
    assert "neither delivered statement nor actual marginal decision effect" in brief["notes"].lower()

    val = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    for token in (
        "acshPublicArgumentHasFirstPartySource",
        "gcc2001KyotoScriptIsExposureNotVerdict",
        "gccStateDepartmentReportedAccessDoesNotProveMethodTransfer",
        "donorActorInstitutionProximityDoesNotEstablishDecisionControl",
    ):
        assert token in val
    assert "import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as Proximity" in val
    assert "recommendationExposureIsNotDirectMethodTransfer" in typed


def test_recycled_claim_family_receipts_preserve_original_root_and_relation():
    """Selected proposition surfaces are not a population study of deniers."""
    from collections import Counter
    path = ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv"
    with path.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    assert len(rows) == 53
    assert len({r["receipt_id"] for r in rows}) == 53
    assert all(r["claim_family"] and r["evidence_objects"] and
               r["relation_to_claim"] and r["nonpromotion_boundary"] for r in rows)
    totals = Counter(r["claim_family"] for r in rows)
    assert len(totals) == 22
    assert totals["US_UNCERTAINTY_STRATEGY"] == 2
    assert totals["API_PROMPTED_58PC"] == 1
    assert totals["GAS_TAX_17B_ANNUAL"] == 8
    assert totals["GAS_INVESTMENT_TAX_83PC"] == 4
    assert totals["GAS_INVESTMENT_SUPPLY_PRICE"] == 4
    assert totals["GAS_TAX_POLICY_SPECIFICATION"] == 3
    assert totals["GAS_TAX_VS_RESERVATION_DENOMINATOR"] == 2
    assert totals["GAS_TAX_TOTAL_21_9B_AEP"] == 2

    by_id = {r["receipt_id"]:r for r in rows}
    assert by_id["H01"]["evidence_objects"] == "ICE_PLAN_1991"
    assert by_id["H02"]["evidence_objects"] == "API_PLAN_1998"
    assert by_id["H02"]["relation_to_claim"] == "similar_strategy_not_copied_text"
    assert "1100" in by_id["H03"]["surface_or_document"]
    assert "58 percent" in by_id["H03"]["numerical_or_rhetorical_payload"]
    assert "unprompted" in by_id["H03"]["nonpromotion_boundary"]

    assert by_id["G01"]["evidence_objects"] == by_id["G03"]["evidence_objects"]
    assert by_id["G03"]["relation_to_claim"] == "credited_reuse_of_named_estimator"
    assert "no company tax" in by_id["G01"]["nonpromotion_boundary"].lower()
    assert by_id["G08"]["evidence_objects"] == by_id["G15"]["evidence_objects"] == "NIGHTLY_JOHNSON_2026"
    assert by_id["G08"]["relation_to_claim"] == "explicit_credited_article_reprint"
    assert by_id["G15"]["relation_to_claim"] == "explicit_original_journalist_credit"


def test_same_gas_headline_two_named_models_not_seven_estimates():
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as stream:
        rows = {r["receipt_id"]:r for r in csv.DictReader(stream)}
    # The same rounded 17b headline appears in policy and news products;
    # institute research (2025) and Arthur D. Little (2026) are two separately
    # NAMED estimators, not certified statistically independent modelling.
    assert rows["G04"]["evidence_objects"] == "TAI_TAX_17B_2025"
    assert rows["G05"]["evidence_objects"] == "FUTURE_ADL_17B_2026"
    assert rows["G09"]["evidence_objects"] == "TAI_TAX_17B_2025|FUTURE_ADL_17B_2026"
    assert rows["G06"]["date"] < rows["G05"]["date"]
    assert "Do not infer" in rows["G06"]["nonpromotion_boundary"]
    assert "not measured revenue" in rows["G04"]["nonpromotion_boundary"]

    assert rows["G17"]["evidence_objects"] == "ACTU_2026_PRIMARY"
    assert "2023-24" in rows["G17"]["numerical_or_rhetorical_payload"]
    assert "not a 2026-27 forecast" in rows["G17"]["nonpromotion_boundary"]
    assert rows["G18"]["numerical_or_rhetorical_payload"].startswith("replace PRRT")
    assert rows["G19"]["numerical_or_rhetorical_payload"].startswith("additional 25%")
    assert rows["G18"]["evidence_objects"] != rows["G19"]["evidence_objects"]
    assert rows["G20"]["evidence_objects"] == "AUS_GOV_RESERVATION_2025"
    assert rows["G21"]["evidence_objects"] == "ACTU_2026_PRIMARY"
    assert "gas production reserved" in rows["G20"]["numerical_or_rhetorical_payload"]
    assert "exported sales revenue" in rows["G21"]["numerical_or_rhetorical_payload"]
    assert "NOT an export revenue tax rate" in rows["G20"]["nonpromotion_boundary"]
    assert rows["G10"]["evidence_objects"] == rows["G11"]["evidence_objects"] == "WOODMAC_AEP_2026"
    assert rows["G22"]["evidence_objects"] == rows["G23"]["evidence_objects"] == "AEP_SURVEY_2025"
    assert "forecast" in rows["G22"]["nonpromotion_boundary"]
    assert "requires revised original actuals" in rows["G23"]["nonpromotion_boundary"]
    assert "not observed national" in rows["G10"]["nonpromotion_boundary"]
    assert rows["G12"]["relation_to_claim"] == "named_adversarial_model_reanalysis"
    assert rows["G14"]["relation_to_claim"] == "attributed_separate_witness_parallel_argument"
    assert rows["G16"]["relation_to_claim"] == "same_argument_no_copied_text_receipt"


def test_recycled_claims_consume_canonical_agda_nonfactorability():
    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    proofs = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    for relation in ("explicitAttributedRepublication", "reportedStatisticRestatement",
                     "parallelEconomicArgument"):
        assert relation + " : RelationKind" in typed
    for receipt in (
        "apiCharltonPromotedPoll1998", "australiaInstitute17B2025",
        "futureGroupArthurDLittle2026", "pocockGas2026",
        "taiGasRoyalty2024", "aepWoodMackenzie2026",
        "nightlyJohnsonGas2026", "hancockJohnsonReprint2026",
        "actu2026OriginalReplacementProposal", "australianGovernmentGasReservation2025",
        "aep2025OriginalFinancialForecast", "aep2026TaxSenateSubmission",
    ):
        assert receipt + " : Typed.SourceReceipt" in owner
    for relation in (
        "iceToAPIUncertaintyStrategicRecurrence", "tai17BRestatedByPocock2026",
        "futureGroup17BRestatedByPocock2026", "tai56PcRoyaltyRestatedByPocock2026",
        "nightlyToHancockExplicitReprint2026", "aepWoodMacStatisticsNotNationalTaxRate",
        "actuReplacementVsAEPAddOnSpecification", "gasReservationIsNot25PcExportLevy",
        "aepForecastToPaidStatusRestatement",
    ):
        assert relation + " : Typed.TypedGenealogyEdge" in owner
    assert "import DASHI.Core.IntersectionalNonFactorability as INF" in owner
    assert "sameHeadlineDistinctGenealogies =\n  INF.nonFactorabilityWitness" in owner
    assert "sameRateDifferentTaxInstrument =\n  INF.nonFactorabilityWitness" in owner
    assert "same17BHeadlineDoesNotIdentifyNamedModelCount" in proofs
    assert "same25PcHeadlineDoesNotIdentifyTaxDesign" in proofs
    assert "donorActorInstitutionProximityDoesNotEstablishDecisionControl" in proofs


def test_aep_21_9b_original_forecast_to_later_paid_public_claim():
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as stream:
        rows = {r["receipt_id"]:r for r in csv.DictReader(stream)}
    assert rows["G22"]["date"] == "2025-07-27"
    assert rows["G23"]["date"] == "2026-04-13"
    assert rows["G22"]["relation_to_claim"] == "first_party_survey_forecast"
    assert rows["G23"]["relation_to_claim"] == "same_association_rounding_and_actuality_promotion"
    assert rows["G22"]["evidence_objects"] == rows["G23"]["evidence_objects"]
    # Original association's published *forecast*, million AUD. Addition
    # verifies the released internal table, NOT actual remitted taxes.
    component_million_aud = (13_484, 1_347, 6_620, 492)
    assert sum(component_million_aud) == 21_943
    assert "13484m company tax + 1347m PRRT + 6620m royalties/excise/fees + 492m other" in rows["G22"]["numerical_or_rhetorical_payload"]
    assert "2024-25" in rows["G22"]["numerical_or_rhetorical_payload"]
    assert "final cash payments" in rows["G22"]["nonpromotion_boundary"]

    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    val = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    assert "aepForecastToPaidStatusRestatement : Typed.TypedGenealogyEdge" in owner
    assert "sameRoundedTaxTotalDifferentSourceStatus =\n  INF.nonFactorabilityWitness" in owner
    assert "sameTaxNumberCannotDetermineSourceStatus" in owner
    assert "same21Point9BNumberDoesNotEstablishActualityStatus" in val
    assert "aep2025ForecastTo2026PaidHeadlineHasSameInstitution" in val



def test_adl_original_three_scenario_bases_and_one_producer():
    """One authored model with three different 25% levy bases, not three replications."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    originals = [rows[k] for k in ("G25", "G26", "G27")]
    assert all(row["evidence_objects"] == "ADL_2026_ORIGINAL" for row in originals)
    assert len({row["locator"] for row in originals}) == 1
    assert all(row["locator"].endswith("final-ad-little-modelling-gas-exports-15.pdf")
               for row in originals)
    assert {row["claim_family"] for row in originals} == {"GAS_TAX_TEN_YEAR_SCENARIOS"}
    assert "95-100bn" in rows["G25"]["numerical_or_rhetorical_payload"]
    assert "28-32bn" in rows["G26"]["numerical_or_rhetorical_payload"]
    assert "9-11bn" in rows["G27"]["numerical_or_rhetorical_payload"]
    assert "AUD8.5/GJ" in rows["G27"]["numerical_or_rhetorical_payload"]
    # Confirm decade model ranges are not ten repetitions of up-to 17bn.
    decade_ranges = [(95, 100), (28, 32), (9, 11)]
    first_year_upper_bound = 17
    assert all(low <= high for low, high in decade_ranges)
    assert all(not (low <= 10 * first_year_upper_bound <= high)
               for low, high in decade_ranges)
    assert rows["G24"]["claim_family"] == "GAS_TAX_17B_ANNUAL"
    assert rows["G24"]["evidence_objects"] == "ADL_2026_ORIGINAL"
    assert "first year" in rows["G24"]["numerical_or_rhetorical_payload"]
    assert "not recurring" in rows["G24"]["nonpromotion_boundary"]
    assert rows["G24"]["date"] < rows["G05"]["date"]
    assert rows["G05"]["evidence_objects"] == "FUTURE_ADL_17B_2026"


def test_adl_client_return_unit_and_resource_rent_denominators():
    """No percentage-point, denominator, or modelled supply promotion."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    assert rows["G28"]["evidence_objects"] == rows["G29"]["evidence_objects"] == "ADL_2026_ORIGINAL"
    assert "percentage points of IRR" in rows["G28"]["numerical_or_rhetorical_payload"]
    assert "percent on average" in rows["G29"]["numerical_or_rhetorical_payload"]
    assert "not the same as" in rows["G28"]["nonpromotion_boundary"]
    assert "not to increase domestic supply overall" in rows["G30"]["numerical_or_rhetorical_payload"]
    assert "not an observed increase" in rows["G30"]["nonpromotion_boundary"]
    assert "6.9 percent resource rent only" in rows["G31"]["numerical_or_rhetorical_payload"]
    assert "25.8 percent total gas-company tax" in rows["G31"]["numerical_or_rhetorical_payload"]
    assert "excludes regular company income tax" in rows["G31"]["nonpromotion_boundary"]


def test_adl_reuses_existing_typed_genealogy_nonfactorability_and_regression():
    """Author/source first; same headline cannot prove one tax design or return unit."""
    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    regression = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    assert owner.count("adlSourceReportPublicRelease2026 : Typed.SourceReceipt") == 1
    assert "Typed.commissionedResearch Typed.primary" in owner
    for receipt in ("adlReportCommissionedAndPublic", "adlSeventeenBFirstYearUpperBoundNotTenYearCash",
                    "adlIRRPointsVersusFutureGroupReturnsPercent"):
        assert receipt + " : Typed.TypedGenealogyEdge" in owner
    for proof in ("adlSameRateDifferentRevenueBases",
                  "adlSame25RateCannotDetermineDecadeRevenue",
                  "samePrintedTwoDifferentReturnUnits", "bareTwoPercentCannotIdentifyReturnUnit"):
        assert proof in owner
    assert owner.count("INF.nonFactorabilityWitness broadBase25 prospective25 refl (λ ())") == 1
    assert "INF.nonFactorabilityWitness twoIRRPercentagePoints twoPercentRelativeReturn refl (λ ())" in owner
    for consumer in ("same25NominalRateCannotDetermineADLTenYearRevenue",
                     "bareTwoPercentCannotDetermineIRRChangeUnits",
                     "adlReturnsUnitSummaryNotAnotherEconomicModel"):
        assert consumer in regression
    assert "headlineNumberRestatementIsNotHistoricalMethodTransfer" in typed



def test_woodmac_original_appendix_overrules_press_only_source_gap():
    """The consultant authored one hypothetical model; client restatements are not copies of nature."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    for key in ("G32", "G33", "G34", "G35", "G36"):
        assert rows[key]["evidence_objects"] == "WOODMAC_ORIGINAL_2026"
        assert rows[key]["locator"].endswith("Wood-Mackenzie-Analysis-of-Proposed-Windfall-Levy.pdf")
    assert rows["G10"]["evidence_objects"] == "WOODMAC_AEP_2026"
    assert "hypothetical 4-tcf" in rows["G32"]["nonpromotion_boundary"].lower()
    assert "US$120/bbl" in rows["G32"]["numerical_or_rhetorical_payload"]
    assert "additional to retained PRRT and CIT" in rows["G33"]["numerical_or_rhetorical_payload"]
    assert "deleting PRRT arithmetically" in rows["G33"]["nonpromotion_boundary"]
    for needed in ("4 tcf", "450 mmcf/d", "27-year", "85% export", "15% domestic"):
        assert needed in rows["G34"]["numerical_or_rhetorical_payload"]
    assert "simplified proxy" in rows["G35"]["numerical_or_rhetorical_payload"]
    assert "not an audit" in rows["G35"]["nonpromotion_boundary"]


def test_woodmac_adl_spot_assumptions_are_model_specific_and_formalised():
    """Equal levy % does not identify which consultant assumes spot export."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    assert rows["G36"]["evidence_objects"] == "WOODMAC_ORIGINAL_2026"
    assert rows["G37"]["evidence_objects"] == "ADL_2026_ORIGINAL"
    assert "no spot sales" in rows["G36"]["numerical_or_rhetorical_payload"]
    assert "27% spot-market" in rows["G37"]["numerical_or_rhetorical_payload"]
    assert rows["G36"]["claim_family"] == rows["G37"]["claim_family"]
    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    regress = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    for proof in ("woodMackenzieOriginalReport2026 : Typed.SourceReceipt",
                  "woodMackenzieOriginalIsAEPCommission : Typed.TypedGenealogyEdge",
                  "woodMackenzieAppendixNotACTUReplacement : Typed.TypedGenealogyEdge",
                  "woodMackenzieNoSpotVersusADLMarginalSpot : Typed.TypedGenealogyEdge",
                  "equal25RateOpposedContractingModels",
                  "same25RateCannotDetermineModelSpotAssumption"):
        assert proof in owner
    assert "woodMackenzieSameRateCannotConcealSpotAssumption" in regress
    assert owner.count("INF.nonFactorabilityWitness woodMacContractedMarket adlMarginalSpotMarket refl (λ ())") == 1



def test_government_reservation_2025_to_2026_policy_design_versions():
    """First-party proposal version transitions, not enacted export-tax evidence."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    assert "15-25 percent of gas production" in rows["G20"]["numerical_or_rhetorical_payload"]
    assert rows["G38"]["date"] == "2026-05-07"
    assert rows["G39"]["date"] == "2026-09-10"
    assert rows["G40"]["date"] == "2026-09-29"
    assert {rows[x]["claim_family"] for x in ("G38", "G39", "G40")} == {
        "GAS_RESERVATION_DESIGN_VERSION"
    }
    assert "20% of LNG exports" in rows["G38"]["numerical_or_rhetorical_payload"]
    assert "1 July 2027" in rows["G38"]["numerical_or_rhetorical_payload"]
    assert "1 January 2028" in rows["G39"]["numerical_or_rhetorical_payload"]
    assert "annual LNG export volumes" in rows["G40"]["numerical_or_rhetorical_payload"]
    assert "calibratable down" in rows["G40"]["numerical_or_rhetorical_payload"]
    assert "not enacted" in rows["G40"]["nonpromotion_boundary"]
    assert rows["G39"]["evidence_objects"] == "GOV_GAS_EXPOSURE_RELEASE_10SEP2026"
    assert rows["G40"]["evidence_objects"] == "DCCEEW_GAS_REFORM_STATUS_29SEP2026"
    assert rows["G39"]["evidence_objects"] != rows["G40"]["evidence_objects"]
    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    regress = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    for declaration in ("governmentReservationMay2026",
                        "governmentReservationSeptember2026",
                        "governmentReservationDepartmentStatus2026",
                        "reservation2025ProductionToMay2026Exports",
                        "reservationMayToSeptemberDutyDate",
                        "reservationDraftChronologyIsNotMethodTransmission"):
        assert declaration in owner
    assert "governmentReservationDutyDateIsDraftSourceSequence" in regress



def test_october_gas_bills_and_levy_homonym_not_tax():
    """An introduced licence-levy bill cannot become a passed 25% export-revenue tax."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    assert rows["G41"]["date"] == rows["G42"]["date"] == rows["G43"]["date"] == "2026-10-14"
    assert rows["G41"]["claim_family"] == rows["G42"]["claim_family"] == "GAS_RESERVATION_BILL_STAGE"
    assert rows["G43"]["claim_family"] == rows["G44"]["claim_family"] == "GAS_LEVY_WORD_COLLISION"
    assert rows["G41"]["evidence_objects"] == "GOV_GAS_BILL_14OCT2026"
    assert rows["G42"]["evidence_objects"] == "HANSARD_GAS_PRINCIPAL_14OCT2026"
    assert rows["G43"]["evidence_objects"] == "HANSARD_GAS_LEVY_14OCT2026"
    assert rows["G44"]["evidence_objects"] == "ADL_2026_ORIGINAL"
    assert rows["G45"]["evidence_objects"] == "HANSARD_GAS_CONSEQUENT_14OCT2026"
    assert "regulatory costs" in rows["G43"]["numerical_or_rhetorical_payload"]
    assert "future regulations" in rows["G43"]["numerical_or_rhetorical_payload"]
    assert "25 percent ad valorem" in rows["G44"]["numerical_or_rhetorical_payload"]
    assert "NOT a 25%" in rows["G43"]["nonpromotion_boundary"]
    assert "at least 90%" in rows["G45"]["numerical_or_rhetorical_payload"]
    assert "up to 10%" in rows["G45"]["numerical_or_rhetorical_payload"]
    assert "not final statute" in rows["G42"]["nonpromotion_boundary"]
    assert rows["G43"]["locator"].startswith("https://www.openaustralia.org.au/debate/")
    assert "mirror" in rows["G43"]["provenance_scope"]

    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    typed = (ROOT / "DASHI/Governance/TypedGenealogyEdgeExact.agda").read_text()
    regress = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    for entry in ("octoberGasBillMinisterialRelease2026", "octoberGasPrincipalMinisterSpeech2026",
                  "octoberGasLevyMinisterSpeech2026", "octoberGasConsequentialMinisterSpeech2026"):
        assert entry + " : Typed.SourceReceipt" in owner
    for entry in ("octoberGasBillsIntroduced2026", "octoberCostRecoveryLevyNotRevenueTax",
                  "octoberAdditionalityNotObservedDeliveredSupply"):
        assert entry + " : Typed.TypedGenealogyEdge" in owner
    assert "legislativeIntroduction : RelationKind" in typed
    assert "legislativeIntroductionDoesNotEstablishHistoricalTransfer" in typed
    assert owner.count("INF.nonFactorabilityWitness\n    administrativeLicenceRecovery exportValueQuarterTax refl (λ ())") == 1
    assert "octoberBareLevyStringNotInstrumentIdentifier" in regress
    assert "octoberBillIsIntroducedNotCertifiedEnacted" in regress


def test_september_distinct_original_document_not_same_object_id():
    """Joint ministerial Sept press and departmental update are different authored files."""
    with (ROOT / "Docs/support/reference/climate_repeated_claim_families_20261026.csv").open(
        newline="", encoding="utf-8"
    ) as handle:
        rows = {r["receipt_id"]: r for r in csv.DictReader(handle)}
    assert rows["G39"]["evidence_objects"] == "GOV_GAS_EXPOSURE_RELEASE_10SEP2026"
    assert rows["G40"]["evidence_objects"] == "DCCEEW_GAS_REFORM_STATUS_29SEP2026"
    assert rows["G39"]["evidence_objects"] != rows["G40"]["evidence_objects"]
    assert rows["G39"]["locator"] != rows["G40"]["locator"]
    assert rows["G39"]["date"] < rows["G40"]["date"]



def test_model_alias_source_counter_not_independent_population():
    """Original-model producer ≠ number of paraphrases, documents, or replications."""
    from scripts.climate_claim_origin_audit import (
        canonical_object, read_ledger, observed_objects, audit,
    )
    rows = read_ledger()
    report = audit(rows)
    assert report["sampled_appearances"] == 53
    assert report["sampled_claim_families"] == 22
    assert report["status"] == "selected-source-provenance-only"
    assert "No national source-concentration estimate" in report["warning"]
    assert canonical_object("FUTURE_ADL_17B_2026") == "ADL_2026_ORIGINAL"
    assert canonical_object("WOODMAC_AEP_2026") == "WOODMAC_ORIGINAL_2026"
    assert canonical_object("HANSARD_GAS_LEVY_14OCT2026") != "ADL_2026_ORIGINAL"
    byid = {r["receipt_id"]: r for r in rows}
    assert observed_objects(byid["G05"]) == observed_objects(byid["G24"])
    assert observed_objects(byid["G10"]) == observed_objects(byid["G32"])
    assert observed_objects(byid["G39"]) != observed_objects(byid["G40"])
    assert observed_objects(byid["G43"]) != observed_objects(byid["G44"])
    m = report["family_audit"]["GAS_TAX_17B_ANNUAL"]
    assert m["sampled_appearances"] == 8
    assert m["named_estimator_model_roots_not_statistical_independence"] == [
        "TAI_TAX_17B_2025", "ADL_2026_ORIGINAL"
    ]
    assert "ADL_2026_ORIGINAL" in m["cited_object_ids"]
    assert "FUTURE_ADL_17B_2026" not in m["cited_object_ids"]
    other = report["family_audit"]["GAS_INVESTMENT_TAX_83PC"]
    assert other["named_estimator_model_roots_not_statistical_independence"] == [
        "WOODMAC_ORIGINAL_2026"
    ]


def test_original_53_row_sample_cannot_certify_national_concentration_agda():
    """Finite two-world nonfactorability reuses the existing Ibrahim machinery."""
    owner = (ROOT / "DASHI/Governance/ClimateGenealogyTypedCasesExact.agda").read_text()
    regression = (ROOT / "DASHI/Governance/EmpiricalGenealogyRound3Regression.agda").read_text()
    assert "samePurposive53AppearanceLedger" in owner
    assert "selectedCorpusCannotDetermineNationalOriginConcentration" in owner
    assert "sameSelectedLedgerDifferentNationalPopulations" in owner
    assert "INF.nonFactorabilityWitness\n    fewAdditionalOriginals manyAdditionalOriginals refl (λ ())" in owner
    assert "selectedClimateCorpusIsNotNationalSourceCensus" in regression
    assert "NationalSourcePopulationCompletion" in owner
    assert "NOT a statistic about Australian national climate denial" in owner


def test_origin_counter_rejects_forced_postdated_model_attribution():
    """An earlier Greens April statement cannot be hard-attributed to later release."""
    from scripts.climate_claim_origin_audit import read_ledger, audit
    rows = read_ledger()
    clone = [dict(row) for row in rows]
    row = next(row for row in clone if row["receipt_id"] == "G06")
    row["relation_to_claim"] = "explicit_source_transfer"
    try:
        audit(clone)
    except ValueError as error:
        assert "April 14 Greens" in str(error)
    else:
        raise AssertionError("Unwitnessed cross-date model transfer promoted")
