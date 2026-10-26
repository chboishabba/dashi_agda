module DASHI.Cognition.AustraliaPoliticalEconomySameObjectCrosswalk20261026Exact where

-- Australian political economy: exact source-type crosswalk, 2026-10-26.
-- Original sources/authors keep authorship: Hanson parliamentary declaration;
-- Hanson first-person radio interview as reported by ABC; published NSWSC
-- Rinehart v Rinehart [2018] NSWSC 1102; DOJ original Bannon statement and
-- Palmer's contradiction; Mandelson forwarded strategy in Epstein corpus.
-- Johl Brown directs the independent case framing; OpenAI ChatGPT assisted
-- this bounded adapter. Do NOT infer coordination, bribery, criminality,
-- policy control or causation from overlap of recipient/person/sector names.
-- Later PR #1251 climate/radio ledgers are sibling code: reviewed, not imported.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.AustraliaRinehartTrumpOneNationAccessBridgeExact as Access
import DASHI.Cognition.QueenslandRinehartCrisafulliTrumpResourceAccessExact as QLD
import DASHI.Cognition.AustraliaMandelsonMiningTaxPoliticalEconomyBridgeExact as Tax
import DASHI.Cognition.EpsteinAustraliaEliteNetworkAcquisitionExact as Australia
import DASHI.Cognition.BannonFaragePalmerAutomatedInfluenceReceiptsExact as Palmer

-- Retain canonical owners rather than reasserting their case events as
-- independently established by this consumer.
oneNationAccessOwner : Access.AustraliaTrumpPoliticalFinanceBoundary
oneNationAccessOwner = Access.canonicalAustraliaTrumpPoliticalFinanceBoundary

queenslandResourceOwner : QLD.QueenslandResourceAccessBoundary
queenslandResourceOwner = QLD.canonicalQueenslandResourceAccessBoundary

australianMiningTaxOwner : Tax.MiningTaxPoliticalEconomyBoundary
australianMiningTaxOwner = Tax.canonicalMiningTaxPoliticalEconomyBoundary

australianEpsteinOwner : Australia.AustraliaAcquisitionBoundary
australianEpsteinOwner = Australia.canonicalAustraliaAcquisitionBoundary

-- Local reported/source-qualified edges that *are* present.
materialSupportAtSourceScope :
  QLD.rinehartMaterialSupportToOneNationPaid queenslandResourceOwner ≡ true
materialSupportAtSourceScope = refl

firstPersonPolicyInputAtSourceScope :
  QLD.rinehartPolicyInputToHansonPaid queenslandResourceOwner ≡ true
firstPersonPolicyInputAtSourceScope = refl

oneNationTrumpAccessReported :
  Access.rinehartTrumpAccessBrokeragePaid oneNationAccessOwner ≡ true
oneNationTrumpAccessReported = refl

mandelsonEpsteinMiningTaxAdviceAtSourceScope :
  Tax.epsteinRecipientOfStrategyPaid australianMiningTaxOwner ≡ true
mandelsonEpsteinMiningTaxAdviceAtSourceScope = refl

-- Negative/counterfactual claims remain UNPAID in the existing owners.
rinaDirectEpsteinConnectionNotEstablished :
  Australia.ginaRinehartDirectRelationshipPaid australianEpsteinOwner ≡ false
rinaDirectEpsteinConnectionNotEstablished = refl

mandelsonAdviceDoesNotPayRuddOutcome :
  Tax.correspondenceCausedRuddRemovalPaid australianMiningTaxOwner ≡ false
mandelsonAdviceDoesNotPayRuddOutcome = refl

policyConsultationNotPartyControl :
  QLD.policyAdviceProvesPartyControl queenslandResourceOwner ≡ false
policyConsultationNotPartyControl = refl

parallelTrumpAccessNotCommonTasking :
  QLD.parallelTrumpAccessProvesCoordination queenslandResourceOwner ≡ false
parallelTrumpAccessNotCommonTasking = refl

bannonStatementNotIndependentPalmerDirection :
  Access.palmerBannonOperationalInfluenceEstablished oneNationAccessOwner ≡ false
bannonStatementNotIndependentPalmerDirection = refl

-- The parent Palmer owner includes an essential later correction:
-- Palmer initially denied *any* contact through a spokesperson, but later
-- described one unsolicited call, while denying campaign direction.
-- Reported admission of contact != original phone record or creative brief.
palmerLaterSingleCallSourceAttributed :
  Palmer.directContactPaid Palmer.bannonPalmerReceipt ≡ true
palmerLaterSingleCallSourceAttributed = refl

palmerCampaignDirectionNotIndependentlyVerified :
  Palmer.independentlyVerifiedInfluencePaid Palmer.bannonPalmerReceipt ≡ false
palmerCampaignDirectionNotIndependentlyVerified = refl

-- Source-status labels: do not silently promote indexed document to
-- first-hand byte inspection, or a litigant/report to a judicial finding.
data AustraliaSourceRole : Set where
  originalParliamentaryDeclaredInterest : AustraliaSourceRole
  originalElectoralRegulatorRule : AustraliaSourceRole
  firstPersonPolicyInterviewReported : AustraliaSourceRole
  originalPartyPolicyPublication : AustraliaSourceRole
  originalFirstPersonPolicyAdvocacy : AustraliaSourceRole
  governmentIndexedAdvocacySubmission : AustraliaSourceRole
  originalNamedCommissionedPolicyModel : AustraliaSourceRole
  originalLimitedGovernmentLegislation : AustraliaSourceRole
  proposedCommercialPartyTenancyReported : AustraliaSourceRole
  publisherConfirmedInKindSupport : AustraliaSourceRole
  namedAssociateDonationReported : AustraliaSourceRole
  judiciallyReportedDocumentSchedule : AustraliaSourceRole
  sourceClaimAndDatedCounterStatement : AustraliaSourceRole
  releasedCorrespondenceReported : AustraliaSourceRole
  separateSiblingReconstruction : AustraliaSourceRole

record AustraliaSourceRoleReceipt : Set where
  constructor australia-source-role-receipt
  field
    role : AustraliaSourceRole
    producer : String
    datedLocator : String
    acquisitionCeiling : String
open AustraliaSourceRoleReceipt public

hansonFloridaFlightsSenateDeclaration : AustraliaSourceRoleReceipt
hansonFloridaFlightsSenateDeclaration = australia-source-role-receipt
  originalParliamentaryDeclaredInterest
  "Pauline Hanson, signed Form A alteration, Registry of Senators Interests, 2025-12-16"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Senators_Interests/-/media/FB79802AD0754CB3AC0564B082B5C10A.ashx"
  "Indexed ORIGINAL Senate PDF text: flights Brisbane-Florida 26 Oct-11 Nov 2025; Hancock Prospecting and Rinehart hospitality; PDF original face 403, no image authentication and no proof of undelivered gift/legal violation."

hansonPolicyConsultationABC : AustraliaSourceRoleReceipt
hansonPolicyConsultationABC = australia-source-role-receipt
  firstPersonPolicyInterviewReported
  "Pauline Hanson; ABC Radio Perth interview, reporters Nicolas Perpitch and Oliver Peterson"
  "https://www.abc.net.au/news/2026-06-11/one-nation-pauline-hanson-gina-rinehart/106787540"
  "First-person quoted/recorded policy consultation within ABC 2026-06-11 reporting; the reprint on Rinehart's website is SAME ABC source, not another independent corroboration."

hansonAircraftCorporateStatement : AustraliaSourceRoleReceipt
hansonAircraftCorporateStatement = australia-source-role-receipt
  publisherConfirmedInKindSupport
  "Hancock Prospecting spokesperson, quoted by ABC political reporters Borys and Greber, 2026-04-29"
  "https://www.abc.net.au/news/2026-04-29/gina-rinehart-gifts-plane-to-pauline-hanson-one-nation/106620808"
  "ABC reports the spokesperson confirmed a Rinehart COMPANY gave a Cirrus G7 aircraft; listed price / broadcast estimate is not an inspected invoice or independent political finance filing."

namedAssociatesOneNationCashSupport : AustraliaSourceRoleReceipt
namedAssociatesOneNationCashSupport = australia-source-role-receipt
  namedAssociateDonationReported
  "Angus and Sarah Aitken; Adam Giles; Ian Plimer, independently named by ABC 2026-04-29"
  "https://www.abc.net.au/news/2026-04-29/gina-rinehart-gifts-plane-to-pauline-hanson-one-nation/106620808"
  "ABC reports AUD 1m Aitkens, AUD 500k Giles, AUD 500k Plimer; DIFFERENT individuals from the Rinehart company aircraft and from the proposed AUD 300k access event; original AEC bank-donor settlement objects not acquired here."

hancockIPA2016And2017JudicialDocument : AustraliaSourceRoleReceipt
hancockIPA2016And2017JudicialDocument = australia-source-role-receipt
  judiciallyReportedDocumentSchedule
  "NSW Supreme Court, Rinehart v Rinehart [2018] NSWSC 1102, para 25"
  "https://www.casechat.au/cases/au/rinehart-v-rinehart-9"
  "Published JUDGMENT reproduces the evidence schedule of HPPL amounts paid or provided to IPA: AUD 2.3m 2016 + AUD 2.2m 2017; the judgment is a judicial source but this link is a REPRINT, not native court site; paid finance NOT earmarked to an API 1998 plan, particular article or One Nation campaign."

bannonPalmerContrarySourceReceipt : AustraliaSourceRoleReceipt
bannonPalmerContrarySourceReceipt = australia-source-role-receipt
  sourceClaimAndDatedCounterStatement
  "Steve Bannon DOJ-released 2019 message to Epstein, followed by Clive Palmer's spokesperson denial as reported by ABC 2026-02-01"
  "https://www.abc.net.au/news/2026-02-01/palmer-denies-bannon-claim-of-election-campaign-influence/106293074"
  "DOJ EFTA01615861 message contains Bannon's assertion about AUD 60m ads; an ABC 2026-02-01 spokesperson initially denied ANY conversation. In early Feb 2026 Palmer later acknowledged a brief unsolicited call while saying ads were already running, but Palmer denies that Bannon directed the campaign. Neither contact nor boast proves a delivery contract."

-- Case-specific nonpromotion gates, not new general proof machinery.
record AustralianPowerPipelineFrontier : Set where
  constructor australian-power-pipeline-frontier
  field
    materialSupportAndFirstPersonPolicyAdvicePresent : Bool
    originalParliamentaryFlightDisclosureIdentified : Bool
    courtReportedHancockIPAPaymentsPresent : Bool
    namedAssociateDonationsDistinctFromAircraft : Bool
    bannonPalmerStatementAndDenialPreserved : Bool
    mandelsonStrategyReachedEpsteinAtSourceScope : Bool
    hansonAttributesSpecificPensionerWorkProposalToRinehart : Bool
    oneNationJan2025PensionerPolicyOfficiallyPublished : Bool
    originalRinehartPolicyInstructionBeforeJan2025Authenticated : Bool
    oneNationUnlimitedPensionerPolicyEnactedInLawVerified : Bool
    aecJulDec2026OldRegimeReturnPublicationPending : Bool
    oldFY2025_26AECAnnualDisclosurePublicationPending : Bool
    publishedDonorAnnualReturnSameAsReportedAprilDonation : Bool
    aecFutureReformThresholdApplicableRetroactively : Bool
    oneNationInternalPolicyAdoptionCausallyProven : Bool
    specificIPAContentBoughtByCourtReportedPayments : Bool
    directRinehartEpsteinRelationProven : Bool
    AustralianCampaignUsedKoganRiponScoresProven : Bool
    QueenslandFastTrackCausedByRinehartConsultationProven : Bool
    wholeAustraliaUSCovertCommandProven : Bool
open AustralianPowerPipelineFrontier public

canonicalAustralianPowerPipelineFrontier : AustralianPowerPipelineFrontier
canonicalAustralianPowerPipelineFrontier = australian-power-pipeline-frontier
  true true true true true true true true false false true true false false false false false false false false

australianMaterialSupportDoesNotProvePolicyCapture :
  oneNationInternalPolicyAdoptionCausallyProven
    canonicalAustralianPowerPipelineFrontier ≡ false
australianMaterialSupportDoesNotProvePolicyCapture = refl

-- Actual producer's publicly dated January 2025 PARTY statement upgrades
-- this to a published election-policy proposal. It is NOT an enacted Act or
-- an authenticated private Rinehart instruction before publication.
oneNationOriginalPartyPensionerPolicyPublished :
  oneNationJan2025PensionerPolicyOfficiallyPublished canonicalAustralianPowerPipelineFrontier ≡ true
oneNationOriginalPartyPensionerPolicyPublished = refl

noDatedPrePublicationRinehartInstructionInspected :
  originalRinehartPolicyInstructionBeforeJan2025Authenticated canonicalAustralianPowerPipelineFrontier ≡ false
noDatedPrePublicationRinehartInstructionInspected = refl

partyElectionPledgeNotAutomaticallyEnactedCommonwealthLaw :
  oneNationUnlimitedPensionerPolicyEnactedInLawVerified canonicalAustralianPowerPipelineFrontier ≡ false
partyElectionPledgeNotAutomaticallyEnactedCommonwealthLaw = refl

aecSecond2026TransitionPublicationNotFirstFYRelease :
  aecJulDec2026OldRegimeReturnPublicationPending canonicalAustralianPowerPipelineFrontier ≡ true
aecSecond2026TransitionPublicationNotFirstFYRelease = refl

hansonAttributedSpecificPensionerPolicyOrigin :
  hansonAttributesSpecificPensionerWorkProposalToRinehart
    canonicalAustralianPowerPipelineFrontier ≡ true
hansonAttributedSpecificPensionerPolicyOrigin = refl

noCurrentAECAnnualReturnWithoutPublication :
  publishedDonorAnnualReturnSameAsReportedAprilDonation
    canonicalAustralianPowerPipelineFrontier ≡ false
noCurrentAECAnnualReturnWithoutPublication = refl

futureReformMustNotRetrospectivelyRewrite2026 :
  aecFutureReformThresholdApplicableRetroactively
    canonicalAustralianPowerPipelineFrontier ≡ false
futureReformMustNotRetrospectivelyRewrite2026 = refl

hancockIPADonationsDoNotProveSpecificEditorialOrder :
  specificIPAContentBoughtByCourtReportedPayments
    canonicalAustralianPowerPipelineFrontier ≡ false
hancockIPADonationsDoNotProveSpecificEditorialOrder = refl

australianCampaignToKoganScoresUnpaid :
  AustralianCampaignUsedKoganRiponScoresProven
    canonicalAustralianPowerPipelineFrontier ≡ false
australianCampaignToKoganScoresUnpaid = refl

australiaGlobalCommonProgrammeNotEstablished :
  wholeAustraliaUSCovertCommandProven
    canonicalAustralianPowerPipelineFrontier ≡ false
australiaGlobalCommonProgrammeNotEstablished = refl


palmerRevisedContactAttribution : AustraliaSourceRoleReceipt
palmerRevisedContactAttribution = australia-source-role-receipt
  sourceClaimAndDatedCounterStatement
  "Clive Palmer first-person public account 2026-02-04 reported by The New Daily, following 2026-02-01 initial ABC spokesperson denial"
  "https://www.thenewdaily.com.au/news/politics/australian-politics/2026/02/04/clive-palmer-steve-bannon-ads"
  "Palmer later says one unsolicited late-night Bannon phone call happened AFTER his 2019 ads were running; contradicts the earlier no-contact claim while denying operational direction. Secondary interview rendering, not original call recording, telco log, or signed campaign creative order."

hansonSpecificPensionerPolicyOriginalTranscript : AustraliaSourceRoleReceipt
hansonSpecificPensionerPolicyOriginalTranscript = australia-source-role-receipt
  firstPersonPolicyInterviewReported
  "Pauline Hanson, first-person 2026 ABC Perth interview replayed in ABC Four Corners 2026-09-28 original transcript"
  "https://www.abc.net.au/news/2026-09-28/one-nation-behind-the-orange-wave/107205072"
  "She expressly attributes her proposed pensioners-work-hours policy to Rinehart. This is first-person origination testimony, NOT an independent parliament-recorded party policy adoption or a demonstrated enactment outcome."

aecOldRegimeAnnualDisclosureGate : AustraliaSourceRoleReceipt
aecOldRegimeAnnualDisclosureGate = australia-source-role-receipt
  originalElectoralRegulatorRule
  "Australian Electoral Commission, financial year 2025-26 Annual returns and 2026/27 transition"
  "https://www.aec.gov.au/Parties_and_Representatives/annual-returns.htm"
  "AEC says FY2025-26 donor annual returns are due 2026-11-17, party returns 2026-10-20, but official publication comes February 2027. Its new calendar-year/threshold regime commences 2027-01-01: do not backdate 2027 $5000 threshold to 2026 $17300 rules."

aecDisclosure2026PublicationOriginal : AustraliaSourceRoleReceipt
aecDisclosure2026PublicationOriginal = australia-source-role-receipt
  originalElectoralRegulatorRule
  "Australian Electoral Commission, 2026-10-26 Farrer by-election financial disclosure release"
  "https://aec.gov.au/media/2026/10-26.htm"
  "AEC expressly dates political-party 2025-26 annual return public inspection to 2027-02-01. A contemporary ABC donor report is not yet the future official annual disclosure and does not conclusively prove beneficiary of funds."

siblingClimateFinanceOwnershipNote : String
siblingClimateFinanceOwnershipNote =
  "PR #1251 original climate genealogy carries HPPL/IPA court receipt plus 1998 API/GCC communications plan (US) and media production/funding; unmerged master sibling, source lineage only, not direct contract or editorial instruction joining Gina, IPA and Palmer, Bannon, Epstein or CA."


oneNationJan15_2025PrimaryPolicyPublication : AustraliaSourceRoleReceipt
oneNationJan15_2025PrimaryPolicyPublication = australia-source-role-receipt
  originalPartyPolicyPublication
  "Pauline Hanson's One Nation, party-authored election policy release, 2025-01-15"
  "https://www.onenation.org.au/one-nation-to-remove-limits-on-pensioners-veterans-earnings"
  "Original PARTY publisher pledges that age and veteran pensioners may work with no means-test payment reduction; directly pays a dated, specific 2025 election policy proposal. Hanson's June 2026 first-person Rinehart attribution is a SEPARATE later original utterance, not evidence of when Rinehart advised her, actual legislative passage, private authorship or a causal experiment."

aecSecondHalf2026TransitionOriginal : AustraliaSourceRoleReceipt
aecSecondHalf2026TransitionOriginal = australia-source-role-receipt
  originalElectoralRegulatorRule
  "Australian Electoral Commission, Transitional Rules for funding and disclosure, checked 2026-10-27"
  "https://www.aec.gov.au/FADTransitionalRules/"
  "AEC distinguishes (A) July 2025-June 2026 old-regime returns published by 2027-02-01; (B) July 2026-Dec 2026 OLD-regime transitional returns due 2027-03-11 and published by 2027-04-22; and (C) Jan-Dec 2027 NEW-regime returns, lower $5000 threshold/expedited donor disclosures. Do not misassign late-2026 events to first old FY return or new 2027 threshold."


------------------------------------------------------------------------
-- PRE-2025 POLICY GENEALOGY AND AN INDEPENDENT PARTIAL ENACTMENT
-- Original authorship stays distinct: Rinehart 2021 self-publication,
-- HPPL/IPA 2022 submissions (indexed via Parliamentary Library), 2022
-- Albanese Government *limited* Work Bonus, One Nation 2025 *unlimited*
-- pledge, Hanson 2026 retrospective acknowledgement. Recurrence or
-- earlier public advocacy does NOT authenticate a private handoff.
------------------------------------------------------------------------

rinehart2021PublishedOriginalAdvocacy : AustraliaSourceRoleReceipt
rinehart2021PublishedOriginalAdvocacy = australia-source-role-receipt
  originalFirstPersonPolicyAdvocacy
  "Gina Rinehart, Speech, National Mining and Related Industries Day, 22 November 2021, page 2"
  "https://www.ginarinehart.com.au/wp-content/uploads/2021/11/FINALV2-Speech-by-Mrs-Gina-Rinehart-to-2021-National-Mining-Related-Industries-Day.pdf"
  "Publisher-held ORIGINAL first-person speech, PDF page 2 screenshot visually inspected; author publicly proposed easing pension income penalties for pensioners choosing to work in Nov 2021. She does not thereby prove a 2021/2024 private briefing to Hanson or exclusive intellectual origin; policy motif had other advocates."

hancockIPA2022IndexedParliamentaryPolicy : AustraliaSourceRoleReceipt
hancockIPA2022IndexedParliamentaryPolicy = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Parliamentary Library, 2022 Workforce Incentive Bill Digest, quotes HPPL Submission 3, 16 Aug 2022, and IPA Submission 6, Aug 2022"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/bd/bd2223a/23bd024"
  "Government Parliamentary Library document INDEXES/QUOTES separate 2022 Hancock and IPA Senate submissions advocating an unlimited Work Bonus, including IPA adjunct fellow Cian Hussey. Parliamentary analysis is not the original submission page-byte receipt (APH original submissions returned 403); shared policy does not prove HPPL bought a specific IPA paper or that either uniquely originated the idea."

albanese2022LimitedWorkBonusAct : AustraliaSourceRoleReceipt
albanese2022LimitedWorkBonusAct = australia-source-role-receipt
  originalLimitedGovernmentLegislation
  "Minister Amanda Rishworth, federal government, 22 Nov 2022 passage statement for Social Services and Other Legislation Amendment (Workforce Incentive) Act 2022"
  "https://formerministers.dss.gov.au/20779/giving-older-australians-the-choice-and-flexibility-to-work/"
  "Original GOVERNMENT report of enacted LIMITED additional AUD4000 Work Bonus income bank (temporary through Dec 2023); NOT removal of all means tests as the independent 2025 One Nation party proposal advocates. Existing partial legislation is a disconfirming alternative causal channel, not proof Rinehart/IPA/One Nation directed the government."

oneNationBrisbaneHQReportedLease : AustraliaSourceRoleReceipt
oneNationBrisbaneHQReportedLease = australia-source-role-receipt
  proposedCommercialPartyTenancyReported
  "One Nation and Hancock Prospecting spokespeople, Barnaby Joyce; ABC/AAP/Guardian original reporting, 5 Oct 2026"
  "https://www.abc.net.au/news/2026-10-05/federal-politics-live-blog-albanese-pre-cop/107228246"
  "Party reportedly intends to lease offices at 160 Wharf St Spring Hill in Rinehart/Hanrine-connected building purchased for reportedly AUD8m. Joyce and Hancock say COMMERCIAL MARKET RENT / no discount. Original executed lease, comparative valuation, fit-out payer and registered land title not authenticated; ownership and prospective tenancy do not pay an unlawful in-kind subsidy."

-- Explicit precise source-scope distinctions.
data PensionerWorkPolicyScope : Set where
  temporaryExtraWorkBonus4000 : PensionerWorkPolicyScope
  unlimitedPensionWorkWithoutPaymentReduction : PensionerWorkPolicyScope

-- Distinct declared policy specifications; not empirical proof of legal
-- effect or uniquely transmitted political authorship.
government2022PolicyScope : PensionerWorkPolicyScope
government2022PolicyScope = temporaryExtraWorkBonus4000

oneNation2025PolicyScope : PensionerWorkPolicyScope
oneNation2025PolicyScope = unlimitedPensionWorkWithoutPaymentReduction


-- POSITIVE CONTROL FOR A REAL COMMISSIONED RESEARCH WORK-PRODUCT:
-- Original signed Deloitte letter, National Seniors named commissioning
-- organisation, explicitly scoped pension policy, model and assumptions.
-- Authenticated PDF source pages 1 and 5 (indexes 0 and 4) visually checked.
-- The paid aggregate HPPL->IPA 2016/17 has no equivalent named 2022
-- project-commission/document-use receipt in current case evidence.
nationalSeniorsDeloitte2022CommissionedModel : AustraliaSourceRoleReceipt
nationalSeniorsDeloitte2022CommissionedModel = australia-source-role-receipt
  originalNamedCommissionedPolicyModel
  "Deloitte Touche Tohmatsu, original letter 2 September 2022 to Ian Henschke (National Seniors Australia Chief Advocate), Let Pensioners Work Age Pension Modelling"
  "https://nationalseniors.com.au/uploads/NSA-Let-Pensioners-Work-Age-Pension-Modelling-FINAL-14112022.pdf"
  "Original National Seniors-hosted Deloitte research PDF, pages 1 and 5 visually inspected: client explicitly engaged Deloitte to model opt-in income-test exemption; 8.3% cost-neutral participation threshold is conditional on DSS/ABS data and authors' assumptions and is NOT reproduced here. Original letter/deliverable status establishes commissioned-policy research, NOT proof invoice payment, exclusive intellectual priority, actual uptake or that Labor/One Nation adopted the Deloitte model."

nationalSeniorsMemberCampaign2022Original : AustraliaSourceRoleReceipt
nationalSeniorsMemberCampaign2022Original = australia-source-role-receipt
  originalFirstPersonPolicyAdvocacy
  "National Seniors Australia, its 2022 original Let Pensioners Work campaign survey/flyer"
  "https://nationalseniors.com.au/uploads/LetPensionersWork-A4FlyerApril13.pdf"
  "First-party original senior-membership policy campaign advocated exemption of employment income from Age Pension income test; survey reports 1249 pension-receiving respondents in 2022. In-house advocacy versus external Deloitte economic modelling are two related National Seniors commissioned/institutional source products, NOT two independent demonstrations of government causal adoption."

-- This named original commissioned research is a genuine purchase/procurement
-- *of expert modelling* (client named) unlike unrelated 2016/17 HPPL/IPA
-- aggregate funding. Do not transport Deloitte's client/forecast to IPA
-- or attribute separate One Nation 2025 draft text to either institution.


------------------------------------------------------------------------
-- 27 OCT 2026: PRIMARY PARLIAMENTARY DOCKET AND TEMPORAL NON-COLLAPSE
-- The government's FEBRUARY 2022 bill was introduced BEFORE AUGUST 2022
-- HPPL/IPA submissions. It lapsed. The SEPTEMBER/NOVEMBER 2022 government
-- bill/Act 55 is a DIFFERENT subsequent legislative object. The 2025 One
-- Nation pledge is a different specification again.
-- Parliamentary submission INDEX records are not authenticated PDF faces,
-- and a submission does not by itself establish bill drafting influence.
------------------------------------------------------------------------

coalitionFeb2022BillDocket : AustraliaSourceRoleReceipt
coalitionFeb2022BillDocket = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Commonwealth Parliament, original March 28 2022 Bills Digest, Carol Ey: Social Services Legislation Amendment (Workforce Incentive) Bill 2022"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/bd/bd2122a/22bd056"
  "Parliamentary original INDEX/analysis: Coalition bill introduced 2022-02-10, lapsed at 2022 election; its Schedules 1 and 2 were later largely reused in a DIFFERENT government bill. Indexed original page, not separately inspected bill PDF. Cannot attribute February drafting to August submissions."

senateSeptember2022MultipleSubmitterDocket : AustraliaSourceRoleReceipt
senateSeptember2022MultipleSubmitterDocket = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Senate Community Affairs Legislation Committee, Enhancing Pensioner and Veteran Workforce Participation 2022 official original submissions register"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceParticipation/Submissions"
  "Official REGISTER uniquely identifies HPPL #3 (DocStore dfaa59de-73b8-4409-ab06-4527c2c6cfd3), IPA #6 (8f9cfa11-5287-40b3-8287-4fbff1f88b80) with separate attachment, and National Seniors #7 (b202b377-58e6-4c7f-97b8-73ef42e74882). Underlying PDF page bytes not inspected here (APH 403/timeout). Distinct producers; register does not establish instructions, a joint commission or enacted adoption."

accciDecember2021IndependentAlternative : AustraliaSourceRoleReceipt
accciDecember2021IndependentAlternative = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Australian Chamber of Commerce and Industry, Dec 2021 pre-budget recommendation as quoted by Carol Ey in 2022 Parliamentary Library bill digest"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/bd/bd2223a/23bd024"
  "PARLIAMENTARY ANALYST QUOTE of independently attributed ACCI recommendation to raise work incentives; not original ACCI statement bytes or an independently proven drafting influence. Distinct institutional policy advocacy undermines an EXCLUSIVE later-origin inference."

act55OfficialStatute : AustraliaSourceRoleReceipt
act55OfficialStatute = australia-source-role-receipt
  originalLimitedGovernmentLegislation
  "Commonwealth of Australia, Social Services and Other Legislation Amendment (Workforce Incentive) Act 2022, No 55, assented 2022-11-23"
  "https://www.legislation.gov.au/C2022A00055"
  "Original official REGISTER: Schedule 1 benefit suspension, Schedule 2 concession cards, Schedule 3 temporary Work Bonus increase. Enactment is not an observed employment increase, permanent unlimited earnings exemption or attribution of the Act to a private lobbyist."

-- These are exact distinctions INSIDE a source-typed finite calendar model.
-- A source-written Agda non-identity witness is NOT an empirical proof of
-- draft causation, legislation effectiveness or missing secret contacts.
data PensionLegislativeObject : Set where
  feb2022CoalitionBill : PensionLegislativeObject
  august2022SenateSubmissions : PensionLegislativeObject
  nov2022Act55 : PensionLegislativeObject
  jan2025OneNationPledge : PensionLegislativeObject

data DistinctObject : Set where

februaryBillIsNotAugustSubmission :
  feb2022CoalitionBill ≡ august2022SenateSubmissions → DistinctObject
februaryBillIsNotAugustSubmission ()

enactedLimitedActIsNotUnlimitedPartyPledge :
  nov2022Act55 ≡ jan2025OneNationPledge → DistinctObject
enactedLimitedActIsNotUnlimitedPartyPledge ()


------------------------------------------------------------------------
-- 27 OCT 2026: THREE PARLIAMENTARY INQUIRIES; DEDUPE BY DOCUMENT + DOCKET.
-- This resolves a previously conflated provenance edge: the Senate examined
-- THREE bills in Feb/Mar, Aug/Sep and Sep/Nov 2022. Each inquiry has a
-- DIFFERENT published submission register; repeat submitters are not
-- independently corroborating the causal effects of their own policy.
------------------------------------------------------------------------

februaryCoalitionSenateRegisterOriginal : AustraliaSourceRoleReceipt
februaryCoalitionSenateRegisterOriginal = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Senate Community Affairs inquiry into Morrison-government Workforce Incentive Bill, referred 10 Feb 2022; submissions due 4 Mar 2022"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceIncentiveBill/Submissions"
  "Official six-entry original committee REGISTER: National Seniors Australia #3, document df5522d8-50d8-4ebb-ad5d-6d7cfd367158. NO HPPL or IPA among SIX listed submissions; this is only bounded absence in this particular public list, not proof neither advised the government. Original PDF face not inspected."

augustDeanSmithBillOriginal : AustraliaSourceRoleReceipt
augustDeanSmithBillOriginal = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Australian Parliament, Senator Dean Smith, Social Services Legislation Amendment (Enhancing Pensioner and Veteran Workforce Participation) Bill 2022, introduced 3 Aug 2022"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/Bills_Search_Results/Result?bId=s1347"
  "Original parliamentary bill status: PRIVATE Senator's bill, NOT PROCEEDING; different from February Coalition government bill, September Albanese government bill, and enacted November Act 55. Dean Smith's bill proposed a $600 fortnightly Work Bonus threshold, not the unlimited model."

septemberAlbaneseBillOriginal : AustraliaSourceRoleReceipt
septemberAlbaneseBillOriginal = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Australian Parliament, Social Services and Other Legislation Amendment (Workforce Incentive) Bill 2022, government bill introduced 28 Sep 2022"
  "https://www.aph.gov.au/Parliamentary_Business/Bills_Legislation/Bills_Lists/Details_page?blsId=legislation%2Fbillslst%2Fbillslst_4f8efdae-7e88-4301-a746-1bc52f0debb8"
  "Official original legislative index: government Bill 28 Sep, House passage 8 Nov, Senate passage 22 Nov, assent 23 Nov as Act No 55. Its temporary $4000 Work Bonus and other schedules were NOT an unlimited pension work-exemption."

octoberGovernmentSenateRegisterOriginal : AustraliaSourceRoleReceipt
octoberGovernmentSenateRegisterOriginal = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Senate Community Affairs inquiry into 28 Sep 2022 Albanese-government Workforce Incentive Bill 2022, submissions due 13 Oct"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceIncentive2022/Submissions"
  "Official 11-entry original REGISTER names DIFFERENT numbered source objects: National Seniors #3 id 146b77ac-abc8-42c9-a937-8f5a45b40c3f, HPPL #9 id 7596775e-a631-40bd-be57-abe6b5efd5a1, IPA #10 id 85a023f4-e99a-45b0-8cf7-785af6302d45. The same organisations had Aug register entries under other IDs, but neither their texts nor independence of their claims is implied. Original PDF faces not inspected."

hancockOct2022OwnSubmissionIndexReceipt : AustraliaSourceRoleReceipt
hancockOct2022OwnSubmissionIndexReceipt = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Hancock Prospecting Pty Ltd, original letter signed/dated 13 Oct 2022, Senate submission 9 to government Workforce Incentive Bill inquiry"
  "https://www.aph.gov.au/DocumentStore.ashx?id=7596775e-a631-40bd-be57-abe6b5efd5a1&subId=722612"
  "Official search index exposes source-original text: HPPL supported an UNLIMITED permanent Work Bonus, opposed 30 Jun 2023 deadline and Centrelink paperwork; original native PDF page face NOT visually authenticated (HTTP 403). A 13 October response cannot have caused the government's 28 September introduction; it may have aimed at later amendment/debate. Repeats the producer's Nov 2021 advocacy, not a new independent witness."

data Pension2022Committee : Set where
  febMorrisonCommittee : Pension2022Committee
  augSmithCommittee : Pension2022Committee
  octAlbaneseCommittee : Pension2022Committee

data Pension2022Producer : Set where
  pensionNationalSeniors : Pension2022Producer
  pensionHancock : Pension2022Producer
  pensionIPA : Pension2022Producer

-- Classification is scoped to the ACTUAL indexed entries, not invented
-- letters, inferred private communications, or any bill-drafting outcome.
data Pension2022IndexedSubmission :
  Pension2022Committee → Pension2022Producer → Set where
  nsaFeb03 : Pension2022IndexedSubmission febMorrisonCommittee pensionNationalSeniors
  hancockAug03 : Pension2022IndexedSubmission augSmithCommittee pensionHancock
  ipaAug06 : Pension2022IndexedSubmission augSmithCommittee pensionIPA
  nsaAug07 : Pension2022IndexedSubmission augSmithCommittee pensionNationalSeniors
  nsaOct03 : Pension2022IndexedSubmission octAlbaneseCommittee pensionNationalSeniors
  hancockOct09 : Pension2022IndexedSubmission octAlbaneseCommittee pensionHancock
  ipaOct10 : Pension2022IndexedSubmission octAlbaneseCommittee pensionIPA

febAndAugCommitteesAreDifferent :
  febMorrisonCommittee ≡ augSmithCommittee → DistinctObject
febAndAugCommitteesAreDifferent ()

augAndOctCommitteesAreDifferent :
  augSmithCommittee ≡ octAlbaneseCommittee → DistinctObject
augAndOctCommitteesAreDifferent ()

-- Same named producer cannot functionally identify a UNIQUE committee:
-- NSA appears on all three published registers. This is a finite
-- no-factorisation statement about docket identity, not source honesty.
pensionSym : {A : Set} {a b : A} → a ≡ b → b ≡ a
pensionSym refl = refl

pensionTrans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
pensionTrans refl refl = refl

sameNsaCannotYieldUniqueCommittee :
  (choose : Pension2022Producer → Pension2022Committee) →
  choose pensionNationalSeniors ≡ febMorrisonCommittee →
  choose pensionNationalSeniors ≡ augSmithCommittee →
  DistinctObject
sameNsaCannotYieldUniqueCommittee choose feb aug =
  febAndAugCommitteesAreDifferent (pensionTrans (pensionSym feb) aug)

-- Within the finite *published* register, a presumed HPPL or IPA
-- February filing has no constructor. Outside-list contact is UNRESOLVED.
noListedHancockFebSubmission :
  Pension2022IndexedSubmission febMorrisonCommittee pensionHancock →
  DistinctObject
noListedHancockFebSubmission ()


------------------------------------------------------------------------
-- PUBLICLY DOCUMENTED INFORMATION REUSE, NOT FINANCIAL COMMISSIONING.
-- Nov 2022 Senate committee original chapter 2, paragraph 2.16:
-- IPA, a separate submitter, referenced National Seniors Australia's
-- 20% older-pensioner survey, estimating 510,000 potential participants.
-- This is an attributed source-to-citation flow; the original survey
-- is NOT independently replicated and the IPA use proves no HPPL tasking.
------------------------------------------------------------------------

senateOct22IPACitesNSASurvey : AustraliaSourceRoleReceipt
senateOct22IPACitesNSASurvey = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Senate Community Affairs Legislation Committee, November 2022 Report on Albanese Workforce Incentive Bill, chapter 2 paragraphs 2.15-2.16"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceIncentive2022/Report/section?id=committees%2Freportsen%2F024985%2F80109"
  "Original public committee ANALYSIS reports IPA's own October submission cited the National Seniors survey claiming 20% pensioner participation if work barriers lowered (~510,000). A documented attributed citation, not source-independent experimental replication; IPA PDF and individual original survey methodology not both re-audited here. No HPPL commissioning, coordinated direction or causal impact follows."

senate2022MultipleDistinctPolicyAmounts : AustraliaSourceRoleReceipt
senate2022MultipleDistinctPolicyAmounts = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Same Senate Committee November 2022 Report chapter 2 paragraphs 2.27-2.31, 2.45-2.51"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceIncentive2022/Report/section?id=committees%2Freportsen%2F024985%2F80109"
  "Committee attributes ALTERNATIVE scopes: ACCI 15600 annual Work Bonus, VCCI extra 10000, NSA 6000 biannual, IPA says government 4000 small, HPPL Oct original indexed letter calls for unlimited Work Bonus. These are separate scoped proposals; the committee recommended the narrower government bill and suggested monitoring, not actual employment outcome verification."

data PensionResearchUse : Set where
  publicThirdPartySurveyCitation : PensionResearchUse
  namedClientConsultantCommission : PensionResearchUse
  specificPrivateSponsorEditorialOrder : PensionResearchUse

documentedNSAtoIPACitation : PensionResearchUse
documentedNSAtoIPACitation = publicThirdPartySurveyCitation

documentedNSAtoDeloitteModelling : PensionResearchUse
documentedNSAtoDeloitteModelling = namedClientConsultantCommission

noCitationEqualsPrivateSponsorEditorialOrder :
  publicThirdPartySurveyCitation ≡ specificPrivateSponsorEditorialOrder →
  DistinctObject
noCitationEqualsPrivateSponsorEditorialOrder ()


------------------------------------------------------------------------
-- 2022 LEGISLATIVE ATTEMPT VERSUS ADOPTION: other policy path.
-- Senate Committee report on the September government bill, chapter 1
-- §§1.41-1.46, traces an actual attempted amendment to a different bill.
------------------------------------------------------------------------

hancockAug2022OwnSubmissionIndexReceipt : AustraliaSourceRoleReceipt
hancockAug2022OwnSubmissionIndexReceipt = australia-source-role-receipt
  governmentIndexedAdvocacySubmission
  "Hancock Prospecting Pty Ltd, official original source index of 16 August 2022 letter, submission 3 to Senator Dean Smith bill inquiry"
  "https://www.aph.gov.au/DocumentStore.ashx?id=dfaa59de-73b8-4409-ab06-4527c2c6cfd3&subId=721185"
  "Parliament original indexed text shows dated 16 August 2022 HPPL letter addressing the Smith bill; actual PDF page image not authenticated (403). SAME corporate advocacy author also filed distinct Oct 13 2022 submission 9 to government bill, so two letters are not two independent institutional witnesses. Original texts/hashes not compared."

september2022RejectedSeniorsHealthCardAmendments : AustraliaSourceRoleReceipt
september2022RejectedSeniorsHealthCardAmendments = australia-source-role-receipt
  originalLimitedGovernmentLegislation
  "Commonwealth Parliament Senate Community Affairs Committee, November 2022 government Workforce Incentive Bill report, chapter 1 paras 1.41-1.46"
  "https://www.aph.gov.au/Parliamentary_Business/Committees/Senate/Community_Affairs/WorkforceIncentive2022/Report/section?id=committees%2Freportsen%2F024985%2F80108"
  "Original parliamentary analysis: Smith bill introduced Aug 3, committee Sept 30 recommended NOT passing; Senate Sept 28 added key Smith-style provisions as amendments to separately titled Seniors Health Card bill; House REJECTED those amendments and Senate did not insist. Attempted parliamentary transfer is documented; it is NOT law, an adopted Smith bill, an HPPL/IPA instruction, or evidence of legislative effect."

data Pension2022LegislativeStage : Set where
  deanSmithPrivateBillProposed : Pension2022LegislativeStage
  seniorsHealthCardAmendmentAttempted : Pension2022LegislativeStage
  seniorsHealthCardAmendmentRejected : Pension2022LegislativeStage
  albaneseWorkforceActAssented : Pension2022LegislativeStage

actualRelatedBillAttemptNotEnactedAct :
  seniorsHealthCardAmendmentRejected ≡ albaneseWorkforceActAssented →
  DistinctObject
actualRelatedBillAttemptNotEnactedAct ()

originalProposalIsNotAcceptedAmendment :
  deanSmithPrivateBillProposed ≡ seniorsHealthCardAmendmentAttempted →
  DistinctObject
originalProposalIsNotAcceptedAmendment ()
