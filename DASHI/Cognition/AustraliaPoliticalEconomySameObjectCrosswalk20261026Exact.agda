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
