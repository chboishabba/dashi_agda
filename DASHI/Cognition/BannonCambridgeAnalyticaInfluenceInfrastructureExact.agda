module DASHI.Cognition.BannonCambridgeAnalyticaInfluenceInfrastructureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.CognitiveWarfareAdmissibleDetectionExact as Detection
import DASHI.Biology.TrumpBannonConsentAttractorBridge as TrumpBannon
import DASHI.Governance.InstitutionalTechniqueTransferCore as Transfer

------------------------------------------------------------------------
-- BANNON / CAMBRIDGE ANALYTICA / SCL / MERCER INFLUENCE INFRASTRUCTURE
--
-- Historical source-backed instantiation surface for the repo's existing
-- observer-relative influence, epistemic-attractor and institutional-technique
-- transfer machinery.  This file does NOT claim that psychographic targeting
-- caused the 2016 US election or Brexit, that every targeted message is
-- cognitive warfare, or that later Bannon-Epstein media work reused Cambridge
-- Analytica methods absent a same-technique receipt.
------------------------------------------------------------------------

data InfluenceEdgeKind : Set where
  bannonCambridgeAnalyticaLeadership : InfluenceEdgeKind
  mercerCambridgeAnalyticaFinance : InfluenceEdgeKind
  sclMilitaryCommunicationsLineage : InfluenceEdgeKind
  facebookDataHarvesting : InfluenceEdgeKind
  voterProfilingAndTargeting : InfluenceEdgeKind
  trumpCampaignVendorRelation : InfluenceEdgeKind
  trumpCampaignPayments : InfluenceEdgeKind
  makeAmericaNumber1VendorOverlap : InfluenceEdgeKind
  fecCoordinationAllegationDisposition : InfluenceEdgeKind
  bannonLeaveEUIntroduction : InfluenceEdgeKind
  aiqSclCambridgeAnalyticaWorkingRelation : InfluenceEdgeKind
  canadianJointPrivacyRegulatorAIQFinding : InfluenceEdgeKind
  ftcKoganNixSeparateIndividualConsents : InfluenceEdgeKind
  ftc2020BannonCivilDemandInvestigation : InfluenceEdgeKind
  ftc2020BannonJudicialShowCauseOrder : InfluenceEdgeKind
  ukElectoralAIQActualCampaignPayments : InfluenceEdgeKind
  breitbartDataConfigIntersection : InfluenceEdgeKind
  psychographicEffectivenessUnresolved : InfluenceEdgeKind
  electionOutcomeCausationUnresolved : InfluenceEdgeKind
  laterBannonEpsteinMediaWork : InfluenceEdgeKind

record InfluenceReceipt : Set where
  constructor influence-receipt
  field
    edgeKind : InfluenceEdgeKind
    sourceIdentity : String
    sourceRole : String
    boundedFinding : String
    relationPaid : Bool
    techniqueTransferPaid : Bool
    electionOutcomeCausationPaid : Bool
    wrongdoingPaidByThisReceipt : Bool
open InfluenceReceipt public

bannonLeadershipReceipt : InfluenceReceipt
bannonLeadershipReceipt = influence-receipt
  bannonCambridgeAnalyticaLeadership
  "UK House of Commons DCMS Committee, Disinformation and fake news: Interim/Final Reports"
  "parliamentary inquiry"
  "The Committee identifies Steve Bannon as a former Vice President of Cambridge Analytica; contemporaneous reporting also records a board role before his 2016 Trump-campaign leadership."
  true false false false

mercerFinanceReceipt : InfluenceReceipt
mercerFinanceReceipt = influence-receipt
  mercerCambridgeAnalyticaFinance
  "UK House of Commons DCMS Committee, Interim Report paragraph 94"
  "parliamentary inquiry"
  "The Committee records Robert Mercer as Cambridge Analytica's principal/majority financial backer and major Republican political donor. This pays ownership/funding structure, not command over every campaign action."
  true false false false

sclLineageReceipt : InfluenceReceipt
sclLineageReceipt = influence-receipt
  sclMilitaryCommunicationsLineage
  "UK House of Commons DCMS Committee, Interim Report paragraph 95"
  "parliamentary inquiry"
  "The Committee records Cambridge Analytica as arising from SCL, whose communications methods had been used in military and conflict settings, and describes CA's focus as data targeting and communications for selected US political candidates."
  true true false false

facebookHarvestReceipt : InfluenceReceipt
facebookHarvestReceipt = influence-receipt
  facebookDataHarvesting
  "US Federal Trade Commission, In the Matter of Cambridge Analytica LLC, 2019"
  "regulatory finding"
  "The FTC found Cambridge Analytica engaged in deceptive practices to harvest personal information from tens of millions of Facebook users."
  true false false true

voterProfilingReceipt : InfluenceReceipt
voterProfilingReceipt = influence-receipt
  voterProfilingAndTargeting
  "US Federal Trade Commission, Cambridge Analytica enforcement materials, 2019"
  "regulatory finding"
  "FTC materials state harvested Facebook information was used to construct personality scores matched with US voter records for voter profiling and targeted advertising services."
  true true false true

trumpCampaignReceipt : InfluenceReceipt
trumpCampaignReceipt = influence-receipt
  trumpCampaignVendorRelation
  "UK House of Commons DCMS Committee + FEC records"
  "parliamentary inquiry / official campaign-finance records"
  "Cambridge Analytica worked for Donald Trump's 2016 presidential campaign. Vendor participation is paid; decisive electoral effect is not."
  true false false false

trumpPaymentsReceipt : InfluenceReceipt
trumpPaymentsReceipt = influence-receipt
  trumpCampaignPayments
  "Federal Election Commission MUR 7351 / Commission records"
  "official campaign-finance record"
  "FEC records identify approximately USD 5.9125 million in 2016-cycle Trump-campaign disbursements to Cambridge Analytica. Payment establishes a substantial vendor relation, not effectiveness or outcome causation."
  true false false false

man1VendorOverlapReceipt : InfluenceReceipt
man1VendorOverlapReceipt = influence-receipt
  makeAmericaNumber1VendorOverlap
  "Federal Election Commission MUR 7147 materials"
  "official enforcement record"
  "FEC materials record Cambridge Analytica serving both the Trump campaign and Mercer-backed Make America Number 1 for campaign/communications-related services. This pays common-vendor topology."
  true false false false

fecDispositionReceipt : InfluenceReceipt
fecDispositionReceipt = influence-receipt
  fecCoordinationAllegationDisposition
  "Federal Election Commission MUR 7147"
  "official enforcement disposition"
  "The FEC investigated common-vendor and coordination allegations but ultimately closed the file; allegations concerning Bannon services were dismissed and the record does not establish illegal Cambridge-Analytica-mediated coordination as an adjudicated fact."
  true false false false

leaveEUIntroductionReceipt : InfluenceReceipt
leaveEUIntroductionReceipt = influence-receipt
  bannonLeaveEUIntroduction
  "UK House of Commons DCMS Final Report paragraphs 264-265"
  "parliamentary inquiry"
  "The Committee received evidence that Bannon introduced Arron Banks/Leave.EU to Cambridge Analytica and records a Leave.EU email seeking a US fundraising and social-media strategy from Cambridge Analytica."
  true true false false

aiqWorkingRelationReceipt : InfluenceReceipt
aiqWorkingRelationReceipt = influence-receipt
  aiqSclCambridgeAnalyticaWorkingRelation
  "UK House of Commons DCMS Final Report paragraphs 148-166"
  "parliamentary inquiry"
  "The Committee found clear evidence of a close working relationship among Cambridge Analytica, SCL and AggregateIQ, including software/data infrastructure and contractual relations."
  true true false false


canadianJointRegulatorAIQReceipt : InfluenceReceipt
canadianJointRegulatorAIQReceipt = influence-receipt
  canadianJointPrivacyRegulatorAIQFinding
  "Canada OPC + BC OIPC ONE joint investigation 2019-11-26, PIPEDA Findings 2019-004, paras 25-32, 68-70, 94, 95-107"
  "independent joint privacy-regulator findings (one investigation, not two)"
  "Canadian regulators concluded AIQ received and used OCEAN psychographic scores for millions of US voters, derived at least in part from data collected by Aleksandr Kogan; reviewed documents indicated AIQ knew of the Kogan source. Investigators found inadequate consent and data safeguards. This pays aggregate score supply and scoped privacy noncompliance, not raw Facebook dataset custody, a particular scored row/version, political efficacy, Aquino origin or Epstein funding."
  true false false true


ftcKoganNixIndividualConsentReceipt : InfluenceReceipt
ftcKoganNixIndividualConsentReceipt = influence-receipt
  ftcKoganNixSeparateIndividualConsents
  "FTC personal consent dockets C-4693 (Kogan) / C-4694 (Nix), Matter 182-3106/182-3107, final 2019-12-18; https://www.ftc.gov/legal-library/browse/cases-proceedings/182-3106-182-3107-aleksandr-kogan-alexander-nix-matter"
  "two separately issued final CONSENT orders within one FTC investigation; not a corporate default finding or independent second investigative team"
  "FTC final individual orders prohibit covered-data misrepresentation and require recipient statements and destruction of GSRApp data and derivative models, subject to preservation rules. Kogan/Nix did not admit complaint allegations, except jurisdiction facts; order publication does not show actual compliance or adjudication of personal allegations."
  true false false false

ukElectoralAiqPaymentsReceipt : InfluenceReceipt
ukElectoralAiqPaymentsReceipt = influence-receipt
  ukElectoralAIQActualCampaignPayments
  "UK Electoral Commission original Vote Leave/BeLeave/Veterans for Britain investigation, 2018, with 2019-08-14 appeal update and 2020-05-07 litigation-cost update; https://www.electoralcommission.org.uk/cy/node/619"
  "independent UK statutory campaign-finance regulator with subsequently corrected judicial/civil enforcement dispositions"
  "Regulator lists five June 2016 payments for AIQ campaign services: three Vote Leave-sourced payments reported in Grimes' returns totalling GBP675315.18, a separate GBP50000 Clake payment, and a GBP100000 Vote Leave-to-Veterans for Britain payment. Vote Leave paid GBP61000 fines and withdrew its appeal; Grimes successfully appealed his GBP20000 sanction in July 2019. This does not identify Facebook/GSR source files or prove electoral outcome effects."
  true false false false


------------------------------------------------------------------------
-- FTC v. BANNON 2020 DISTINCT ORIGINAL FEDERAL COURT PROCEEDING
-- Federal FTC petition and reply are ONE government litigant/root.
-- Bannon's response is a separate *adversarial* litigant statement,
-- neither a judicial finding nor an independent examination of his data.
------------------------------------------------------------------------

ftc2020BannonCIDPetitionReceipt : InfluenceReceipt
ftc2020BannonCIDPetitionReceipt = influence-receipt
  ftc2020BannonCivilDemandInvestigation
  "FTC v. Stephen K. Bannon, DDC 1:20-mc-00111-CRC, FTC petition ECF1 2020-11-09; https://www.ftc.gov/system/files/documents/cases/01_redacted_petition_memo_iso_exhibits_proposed_order.pdf"
  "original FTC court pleading / agency investigative allegation, NOT civil or criminal merits judgment"
  "FTC formally sought to enforce Bannon's 2019 civil investigative demand for a hearing about possible individual responsibility for Cambridge Analytica's data practices. FTC petition says he answered interrogatories and supplied documents during January-February 2020 but contested his later hearing attendance. Neither those underlying responses nor a final merits disposition is authenticated here."
  true false false false

ftc2020BannonRespondentOppositionReceipt : InfluenceReceipt
ftc2020BannonRespondentOppositionReceipt = influence-receipt
  ftc2020BannonCivilDemandInvestigation
  "FTC v. Stephen K. Bannon, DDC 1:20-mc-00111-CRC, Bannon opposition ECF12 2020-12-09; https://www.ftc.gov/system/files/documents/cases/12_bannon_opposition_to_petition_to_enforce_cid.pdf"
  "original independent opposing litigant pleading / attributed defence, NOT judicial exoneration"
  "Bannon denied involvement in or knowledge of Cambridge Analytica's alleged Facebook data wrongdoing and asserted prior document production and Fifth Amendment burdens. His sworn interrogatories and the case's ultimate outcome were not independently audited; his denial and the FTC's assertions must both remain visible."
  true false false false


ftc2020BannonJudicialShowCauseReceipt : InfluenceReceipt
ftc2020BannonJudicialShowCauseReceipt = influence-receipt
  ftc2020BannonJudicialShowCauseOrder
  "FTC v. Stephen K. Bannon, DDC 1:20-mc-00111-CRC, Judge Christopher R. Cooper, 2020-11-18 ECF5; https://www.ftc.gov/system/files/documents/cases/05_order_to_show_cause_0.pdf"
  "signed original federal judicial PROCEDURAL order, separate court producer from FTC litigant"
  "Court found good cause to schedule an order-to-show-cause hearing about enforcing the 2019 FTC civil investigative demand, not to adjudicate consumer-privacy misconduct or enter a final enforcement disposition. The original November 18 order is visibly signed as the judge's court order; the outcome of later hearings is not authenticated in this acquisition."
  true false false false

ftc2020BannonReplyReceipt : InfluenceReceipt
ftc2020BannonReplyReceipt = influence-receipt
  ftc2020BannonCivilDemandInvestigation
  "FTC v. Stephen K. Bannon, DDC 1:20-mc-00111-CRC, FTC reply ECF13 2020-12-18; https://www.ftc.gov/system/files/documents/cases/13_ftcs_reply_iso_petition.pdf"
  "same FTC prosecutor root as original petition; reply is not independent corroboration"
  "FTC disputed the respondent's delay, Fifth Amendment and duplicative-testimony arguments and again requested enforcement of the hearing demand. Pleadings establish litigants' positions and procedural requests, not a resolved personal-liability finding or a Bannon-to-Epstein technology transfer."
  true false false false

breitbartConfigReceipt : InfluenceReceipt
breitbartConfigReceipt = influence-receipt
  breitbartDataConfigIntersection
  "UK House of Commons DCMS Final Report paragraph 165"
  "parliamentary inquiry"
  "The Committee records an AIQ repository config file showing technical interplay involving AIQ, Cambridge Analytica and Breitbart, while noting Bannon's roles at Breitbart and Cambridge Analytica. This pays an infrastructure intersection, not common-command over all outputs."
  true true false false

psychographicEffectivenessReceipt : InfluenceReceipt
psychographicEffectivenessReceipt = influence-receipt
  psychographicEffectivenessUnresolved
  "Nature 2018 review plus later experimental literature on political microtargeting"
  "scientific evidence boundary"
  "The scientific evidence does not establish Cambridge Analytica's claimed psychographic effectiveness as a universal or election-decisive mechanism; later studies find microtargeting effects to be context-dependent."
  true false false false

electionOutcomeBoundaryReceipt : InfluenceReceipt
electionOutcomeBoundaryReceipt = influence-receipt
  electionOutcomeCausationUnresolved
  "cross-source evidence boundary"
  "No source used here establishes that Cambridge Analytica caused Trump's 2016 victory or the Brexit result. Campaign participation, targeting capability and outcome causation remain distinct."
  true false false false

laterEpsteinMediaReceipt : InfluenceReceipt
laterEpsteinMediaReceipt = influence-receipt
  laterBannonEpsteinMediaWork
  "2026 released Epstein/Bannon correspondence and video reporting; separately formalised in TrumpMarALagoBannonBridgeExact"
  "later historical relation"
  "Bannon later advised Epstein on media presentation and political/media strategy. Temporal/personnel continuity makes technique-reuse a valid acquisition question, but this receipt does not establish Cambridge Analytica/SCL methods were used for Epstein."
  true false false false

canonicalInfluenceReceipts : List InfluenceReceipt
canonicalInfluenceReceipts =
  bannonLeadershipReceipt
  ∷ mercerFinanceReceipt
  ∷ sclLineageReceipt
  ∷ facebookHarvestReceipt
  ∷ voterProfilingReceipt
  ∷ trumpCampaignReceipt
  ∷ trumpPaymentsReceipt
  ∷ man1VendorOverlapReceipt
  ∷ fecDispositionReceipt
  ∷ leaveEUIntroductionReceipt
  ∷ aiqWorkingRelationReceipt
  ∷ canadianJointRegulatorAIQReceipt
  ∷ ftcKoganNixIndividualConsentReceipt
  ∷ ftc2020BannonCIDPetitionReceipt
  ∷ ftc2020BannonJudicialShowCauseReceipt
  ∷ ftc2020BannonRespondentOppositionReceipt
  ∷ ftc2020BannonReplyReceipt
  ∷ ukElectoralAiqPaymentsReceipt
  ∷ breitbartConfigReceipt
  ∷ psychographicEffectivenessReceipt
  ∷ electionOutcomeBoundaryReceipt
  ∷ laterEpsteinMediaReceipt
  ∷ []

------------------------------------------------------------------------
-- Operational influence loop.
------------------------------------------------------------------------

record PoliticalInfluenceLoop : Set where
  constructor political-influence-loop
  field
    acquireOrInferData : Bool
    resolveAudience : Bool
    segmentOrScoreAudience : Bool
    selectMessageOrIntervention : Bool
    routeThroughPlatformOrMedia : Bool
    observeResponse : Bool
    iterate : Bool
    electionOutcomeGuaranteed : Bool
open PoliticalInfluenceLoop public

canonicalCambridgeAnalyticaLoop : PoliticalInfluenceLoop
canonicalCambridgeAnalyticaLoop = political-influence-loop
  true true true true true true true false

------------------------------------------------------------------------
-- Cross-pollination with existing formal machinery.
------------------------------------------------------------------------

cognitiveDetectionBoundary : Detection.CognitiveDetectionBoundary
cognitiveDetectionBoundary = Detection.canonicalCognitiveDetectionBoundary

trumpBannonPriorArt : TrumpBannon.TrumpBannonConsentAttractorReceipt
trumpBannonPriorArt = TrumpBannon.canonicalTrumpBannonConsentAttractorReceipt

techniqueTransferBoundary : Transfer.InstitutionalTechniqueTransferBoundary
techniqueTransferBoundary = Transfer.canonicalInstitutionalTechniqueTransferBoundary

record BannonInfluenceInfrastructureBoundary : Set where
  constructor bannon-influence-infrastructure-boundary
  field
    bannonCAMercerSCLInfrastructurePaid : Bool
    targetedPoliticalInfluenceCapabilityPaid : Bool
    deceptiveFacebookDataHarvestingPaid : Bool
    crossAtlanticBrokeragePaid : Bool
    militaryToPoliticalTechniqueLineagePaid : Bool
    trumpCAMajorVendorPaymentsPaid : Bool
    campaignSuperPACCommonVendorTopologyPaid : Bool
    illegalCoordinationAdjudicated : Bool
    psychographicEfficacyUniversallyEstablished : Bool
    trumpVictoryCausedByCambridgeAnalytica : Bool
    brexitCausedByCambridgeAnalytica : Bool
    laterEpsteinMediaWorkProvesTechniqueReuse : Bool
    cambridgeAnalyticaRelationshipCreatesEpsteinRelationship : Bool
open BannonInfluenceInfrastructureBoundary public

canonicalBannonInfluenceInfrastructureBoundary : BannonInfluenceInfrastructureBoundary
canonicalBannonInfluenceInfrastructureBoundary = bannon-influence-infrastructure-boundary
  true true true true true true true false false false false false false

------------------------------------------------------------------------
-- Attribution / causal firewalls.
------------------------------------------------------------------------

data TargetingCapabilityImpliesPersuasion : Set where
data CampaignVendorImpliesElectionCause : Set where
data MilitaryLineageImpliesMilitaryOperation : Set where
data DataHarvestImpliesEveryTargetWasManipulated : Set where
data BreitbartConfigImpliesUnifiedCommand : Set where
data CommonVendorImpliesIllegalCoordination : Set where
data BannonContinuityImpliesTechniqueReuse : Set where
data CambridgeAnalyticaImpliesEpsteinCoordination : Set where

targetingCapabilityDoesNotCreatePersuasion : TargetingCapabilityImpliesPersuasion → ⊥
targetingCapabilityDoesNotCreatePersuasion ()

vendorRelationDoesNotCreateElectionCause : CampaignVendorImpliesElectionCause → ⊥
vendorRelationDoesNotCreateElectionCause ()

militaryLineageDoesNotCreateMilitaryOperation : MilitaryLineageImpliesMilitaryOperation → ⊥
militaryLineageDoesNotCreateMilitaryOperation ()

dataHarvestDoesNotCreateUniversalManipulation : DataHarvestImpliesEveryTargetWasManipulated → ⊥
dataHarvestDoesNotCreateUniversalManipulation ()

configIntersectionDoesNotCreateUnifiedCommand : BreitbartConfigImpliesUnifiedCommand → ⊥
configIntersectionDoesNotCreateUnifiedCommand ()

commonVendorDoesNotCreateIllegalCoordination : CommonVendorImpliesIllegalCoordination → ⊥
commonVendorDoesNotCreateIllegalCoordination ()

bannonContinuityDoesNotCreateTechniqueReuse : BannonContinuityImpliesTechniqueReuse → ⊥
bannonContinuityDoesNotCreateTechniqueReuse ()

cambridgeAnalyticaDoesNotCreateEpsteinCoordination : CambridgeAnalyticaImpliesEpsteinCoordination → ⊥
cambridgeAnalyticaDoesNotCreateEpsteinCoordination ()


------------------------------------------------------------------------
-- 2026-10-27: MUR 7351 / FTC CID source-identity, disposition and
-- corroboration ceilings. See original FEC legal record, separate FTC
-- original docket and Jose Pagliery's 2021 firsthand reporting.
-- Source attribution: original FEC commissioners, FTC agency/counsel,
-- district judge and reporter separately; Johl Brown directs analytic
-- boundary, OpenAI ChatGPT assists reconstruction.
------------------------------------------------------------------------

data BannonCAMatter : Set where
  fecMUR7351ForeignNationalContributions : BannonCAMatter
  ftcCID20mc00111CooperProcedure : BannonCAMatter
  ftcCAMatter9389CompanyMerits : BannonCAMatter

data UnavailableMatterIdentity : Set where

fecClosureCannotCloseFTCBannonCID :
  fecMUR7351ForeignNationalContributions ≡ ftcCID20mc00111CooperProcedure →
  UnavailableMatterIdentity
fecClosureCannotCloseFTCBannonCID ()

ftcCACorporateOrderIsNotBannonCIDDisposition :
  ftcCAMatter9389CompanyMerits ≡ ftcCID20mc00111CooperProcedure →
  UnavailableMatterIdentity
ftcCACorporateOrderIsNotBannonCIDDisposition ()

data OriginalProceedingSourceRole : Set where
  federalElectionCommissionCaseRecord : OriginalProceedingSourceRole
  federalTradeCommissionCaseRecord : OriginalProceedingSourceRole
  contemporaneousOriginalReporter : OriginalProceedingSourceRole

record BannonCASeparateLegalReceipt : Set where
  constructor bannon-ca-legal-receipt
  field
    producerRole : OriginalProceedingSourceRole
    sourceName : String
    originalLocator : String
    evidentialCeiling : String
    sourceShowsFileClosed : Bool
    signedFTCCIDFinalOrderInspected : Bool
    provesBannonPersonalPrivacyWrongdoing : Bool
open BannonCASeparateLegalReceipt public

fecMUR7351OriginalClosureReceipt : BannonCASeparateLegalReceipt
fecMUR7351OriginalClosureReceipt = bannon-ca-legal-receipt
  federalElectionCommissionCaseRecord
  "US Federal Election Commission MUR #7351 original disposition, Cambridge Analytica LLC and separately listed respondents including Stephen K. Bannon"
  "https://www.fec.gov/data/legal/matter-under-review/7351/"
  "Official FEC HTML reports 5-0 vote to CLOSE FEC file; Bannon listed Dismissed-Other. Earlier reason-to-believe votes regarding some named respondents are preliminary and NOT an adjudication. 7350/7351 shared FEC acts are not independent investigations; closure is NOT the distinct FTC CID judicial disposition."
  true false false

ftcBannonDocketOriginalPublicIndexReceipt : BannonCASeparateLegalReceipt
ftcBannonDocketOriginalPublicIndexReceipt = bannon-ca-legal-receipt
  federalTradeCommissionCaseRecord
  "Federal Trade Commission v Stephen K Bannon, District of Columbia 1:20-mc-00111-CRC; FTC publisher original case chronology"
  "https://www.ftc.gov/legal-library/browse/cases-proceedings/bannon-stephen-k"
  "FTC public index lists original petition, respondent defence, judge's show-cause order, agency reply to 18 Dec 2020. Original signed Jan 2021 petition-grant/order and compliance/closure NOT inspected here."
  false false false

paglieryJan2021CourtRulingReporting : BannonCASeparateLegalReceipt
paglieryJan2021CourtRulingReporting = bannon-ca-legal-receipt
  contemporaneousOriginalReporter
  "Jose Pagliery, The Daily Beast, October 2021 originally reported judicial grant of the FTC CID petition"
  "https://www.thedailybeast.com/jan-6-committee-plans-to-hold-steve-bannon-in-criminal-contempt"
  "Contemporaneous reporter asserts Judge Christopher Cooper granted petition in January 2021; this is NOT signed court-order authentication or verification that compelled testimony occurred. Distinct from Jan 6 congressional subpoena and federal border-wall pardon."
  false false false
