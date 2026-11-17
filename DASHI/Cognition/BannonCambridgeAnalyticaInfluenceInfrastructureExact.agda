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
