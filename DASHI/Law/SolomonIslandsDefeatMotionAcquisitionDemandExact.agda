module DASHI.Law.SolomonIslandsDefeatMotionAcquisitionDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as Diligence
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search
import DASHI.Law.SolomonIslandsDefeatMotionProvenanceExact as Provenance
import DASHI.Law.SolomonIslandsForeignInterferenceSourceLegalWeldExact as Weld

------------------------------------------------------------------------
-- PRIMARY-THREAD / RELAY-TOPOLOGY ACQUISITION DEMAND
--
-- Broader reporting identifies the downstream political exhortation as Sade's
-- own message after forwarding the Australian High Commission update.  The
-- exact live residual is therefore primary verification of the thread topology,
-- not proof that an Australian actor authored the defeat-motion sentence.
------------------------------------------------------------------------

data MessageRequirement : Set where
  acquireOriginalWhatsAppThread : MessageRequirement
  establishForwardingSenderRecipientTopology : MessageRequirement
  authenticateThreadContentAndOrder : MessageRequirement
  testAustralianConditionality : MessageRequirement

requirementGap : MessageRequirement → Diligence.SourceDiligenceGap
requirementGap acquireOriginalWhatsAppThread = Diligence.primarySourceNotSearched
requirementGap establishForwardingSenderRecipientTopology = Diligence.sameObjectUnresolved
requirementGap authenticateThreadContentAndOrder = Diligence.propositionSupportUnresolved
requirementGap testAustralianConditionality = Diligence.interpretationBoundaryOpen

requiredProducer : MessageRequirement → Search.ProducerClass
requiredProducer r = Diligence.producerForSourceDiligenceGap (requirementGap r)

record MessageAcquisition : Set where
  constructor message-acquisition
  field
    targetRequirement : MessageRequirement
    targetGap : Diligence.SourceDiligenceGap
    producer : Search.ProducerClass
    acquisitionReference : String

open MessageAcquisition public

acquisitionGap : MessageAcquisition → Diligence.SourceDiligenceGap
acquisitionGap = targetGap

acquisitionProducer : MessageAcquisition → Search.ProducerClass
acquisitionProducer = producer

messageAcquisitionAlignment :
  Bound.AcquisitionAlignment
    MessageRequirement
    Diligence.SourceDiligenceGap
    Search.ProducerClass
    MessageAcquisition
messageAcquisitionAlignment = Bound.acquisition-alignment
  requirementGap
  requiredProducer
  acquisitionGap
  acquisitionProducer

originalThreadAcquisition : MessageAcquisition
originalThreadAcquisition = message-acquisition
  acquireOriginalWhatsAppThread
  Diligence.primarySourceNotSearched
  Search.propositionSourceProducer
  "Acquire the original WhatsApp thread/screenshots/export preserving forwarding markers, sender, recipient, timestamps, message order and surrounding context"

currentOriginalThreadDemand :
  Bound.BoundAcquisitionDemand
    messageAcquisitionAlignment
    acquireOriginalWhatsAppThread
    Diligence.primarySourceNotSearched
currentOriginalThreadDemand = Bound.bound-acquisition-demand
  originalThreadAcquisition
  refl
  refl
  refl

currentDemandPaysExactResidual :
  Bound.acquisitionResidual messageAcquisitionAlignment
    (Bound.acquisition currentOriginalThreadDemand)
  ≡ requirementGap acquireOriginalWhatsAppThread
currentDemandPaysExactResidual =
  Bound.acquisitionPaysSelectedResidual currentOriginalThreadDemand

currentDemandUsesExactProducer :
  Bound.acquisitionProducer messageAcquisitionAlignment
    (Bound.acquisition currentOriginalThreadDemand)
  ≡ requiredProducer acquireOriginalWhatsAppThread
currentDemandUsesExactProducer =
  Bound.acquisitionUsesSelectedProducer currentOriginalThreadDemand

------------------------------------------------------------------------
-- Evidence ladder.
------------------------------------------------------------------------

data MessageEvidenceStage : Set where
  twoStageRelayReported : MessageEvidenceStage
  originalThreadAcquired : MessageEvidenceStage
  threadAuthenticated : MessageEvidenceStage
  relayTopologyPrimaryWelded : MessageEvidenceStage
  conditionalityReviewEligible : MessageEvidenceStage
  legalFitEligible : MessageEvidenceStage

record CurrentMessageEvidenceState : Set where
  constructor current-message-evidence-state
  field
    stage : MessageEvidenceStage
    twoStageRelayReportedByNamedSources : Bool
    twoStageRelayReportedByNamedSourcesIsTrue :
      twoStageRelayReportedByNamedSources ≡ true
    originalThreadInHand : Bool
    originalThreadInHandIsFalse : originalThreadInHand ≡ false
    threadAuthenticationPaid : Bool
    threadAuthenticationPaidIsFalse : threadAuthenticationPaid ≡ false
    relayTopologyPrimaryPaid : Bool
    relayTopologyPrimaryPaidIsFalse : relayTopologyPrimaryPaid ≡ false
    australianConditionalityAnalysisEligible : Bool
    australianConditionalityAnalysisEligibleIsFalse :
      australianConditionalityAnalysisEligible ≡ false

open CurrentMessageEvidenceState public

currentMessageEvidenceState : CurrentMessageEvidenceState
currentMessageEvidenceState = current-message-evidence-state
  twoStageRelayReported
  true refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Search intent for the exact first live residual.
------------------------------------------------------------------------

currentPrimaryThreadSearchIntent : Search.SearchIntent
currentPrimaryThreadSearchIntent = Search.searchIntent
  "SolomonIslandsForeignInterferenceSourceLegalWeldExact.currentSourceLegalResidual"
  "authenticate the primary WhatsApp/thread topology connecting the High Commission update, Sade forwarding and Sade's downstream political message"
  Search.propositionSourceProducer
  Search.exploitKnownResidual
  "Solomon Islands / Australia bilateral political communication"
  "late August to 6 September 2026, centred on the no-confidence motion and treaty negotiations"
  Search.primaryTextRequired
  "High Commission -> Sade upstream message and Sade -> coalition downstream message must remain separately authored edges even if adjacent in one thread"
  "ABC-authenticated Roach treaty/funding message; AAP report that Sade forwarded the update and sent his own coalition-directed message; Opposition-published defeat-motion wording"
  "primary artifact must preserve forwarding markers, sender, recipient, timestamp, adjacency/context and exact content"
  "exclude republications and do not treat Sade's downstream language as Australian speech without an independent authorship/agency bridge"
  (Search.searchBudget 6 10 3 "narrow acquisition budget: primary thread first; stop when relay same-object provenance is paid")
  "Solomon WhatsApp relay-topology primary acquisition intent"

currentProducerIsPropositionSourceProducer :
  Search.producerClass currentPrimaryThreadSearchIntent ≡ Search.propositionSourceProducer
currentProducerIsPropositionSourceProducer = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RepeatedSecondaryReportPaysPrimaryThreadDemand : Set where
data SadeForwardingTransfersAustralianAuthorship : Set where
data PrimaryThreadAcquisitionProvesConditionality : Set where
data DomesticUseAutomaticallyProvesForeignIntent : Set where

secondaryRepetitionDoesNotPayPrimaryThread :
  RepeatedSecondaryReportPaysPrimaryThreadDemand → ⊥
secondaryRepetitionDoesNotPayPrimaryThread ()

forwardingDoesNotTransferAustralianAuthorship :
  SadeForwardingTransfersAustralianAuthorship → ⊥
forwardingDoesNotTransferAustralianAuthorship ()

threadAcquisitionDoesNotProveConditionalityByExistence :
  PrimaryThreadAcquisitionProvesConditionality → ⊥
threadAcquisitionDoesNotProveConditionalityByExistence ()

domesticUseDoesNotAutoProveForeignIntent :
  DomesticUseAutomaticallyProvesForeignIntent → ⊥
domesticUseDoesNotAutoProveForeignIntent ()

currentResidualReference : String
currentResidualReference = Weld.nextExactProducer Weld.currentSourceLegalResidual
