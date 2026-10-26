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
    pensionerPolicyEnactedInCommonwealthLawVerified : Bool
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
  pensionerPolicyEnactedInCommonwealthLawVerified canonicalAustralianPowerPipelineFrontier ≡ false
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
