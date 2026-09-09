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
-- DEFEAT-MOTION PRIMARY-ARTIFACT ACQUISITION DEMAND
--
-- This module pays the introspective routing step only.  It binds the exact
-- live residual to the exact repository-native producer class.  Retrieval of
-- another report repeating the Opposition statement cannot pay this demand.
------------------------------------------------------------------------

data MessageRequirement : Set where
  acquireOriginalDefeatMotionArtifact : MessageRequirement
  establishSenderRecipientThreadIdentity : MessageRequirement
  authenticateArtifactContent : MessageRequirement

requirementGap : MessageRequirement → Diligence.SourceDiligenceGap
requirementGap acquireOriginalDefeatMotionArtifact = Diligence.primarySourceNotSearched
requirementGap establishSenderRecipientThreadIdentity = Diligence.sameObjectUnresolved
requirementGap authenticateArtifactContent = Diligence.propositionSupportUnresolved

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

originalArtifactAcquisition : MessageAcquisition
originalArtifactAcquisition = message-acquisition
  acquireOriginalDefeatMotionArtifact
  Diligence.primarySourceNotSearched
  Search.propositionSourceProducer
  "Acquire the original message/thread artifact containing 'stand together to defeat this Motion', preserving sender, recipient, timestamp, message order and surrounding messages"

currentOriginalArtifactDemand :
  Bound.BoundAcquisitionDemand
    messageAcquisitionAlignment
    acquireOriginalDefeatMotionArtifact
    Diligence.primarySourceNotSearched
currentOriginalArtifactDemand = Bound.bound-acquisition-demand
  originalArtifactAcquisition
  refl
  refl
  refl

currentDemandPaysExactResidual :
  Bound.acquisitionResidual messageAcquisitionAlignment
    (Bound.acquisition currentOriginalArtifactDemand)
  ≡ requirementGap acquireOriginalDefeatMotionArtifact
currentDemandPaysExactResidual =
  Bound.acquisitionPaysSelectedResidual currentOriginalArtifactDemand

currentDemandUsesExactProducer :
  Bound.acquisitionProducer messageAcquisitionAlignment
    (Bound.acquisition currentOriginalArtifactDemand)
  ≡ requiredProducer acquireOriginalDefeatMotionArtifact
currentDemandUsesExactProducer =
  Bound.acquisitionUsesSelectedProducer currentOriginalArtifactDemand

------------------------------------------------------------------------
-- Evidence ladder.
------------------------------------------------------------------------

data MessageEvidenceStage : Set where
  oppositionReportedSentence : MessageEvidenceStage
  originalArtifactAcquired : MessageEvidenceStage
  artifactAuthenticated : MessageEvidenceStage
  senderRecipientThreadWelded : MessageEvidenceStage
  legalFitEligible : MessageEvidenceStage

record CurrentMessageEvidenceState : Set where
  constructor current-message-evidence-state
  field
    stage : MessageEvidenceStage
    oppositionSentencePublished : Bool
    oppositionSentencePublishedIsTrue : oppositionSentencePublished ≡ true
    originalArtifactInHand : Bool
    originalArtifactInHandIsFalse : originalArtifactInHand ≡ false
    artifactAuthenticationPaid : Bool
    artifactAuthenticationPaidIsFalse : artifactAuthenticationPaid ≡ false
    australianSenderSameObjectPaid : Bool
    australianSenderSameObjectPaidIsFalse : australianSenderSameObjectPaid ≡ false
    conditionalityCoercionAnalysisEligible : Bool
    conditionalityCoercionAnalysisEligibleIsFalse :
      conditionalityCoercionAnalysisEligible ≡ false

open CurrentMessageEvidenceState public

currentMessageEvidenceState : CurrentMessageEvidenceState
currentMessageEvidenceState = current-message-evidence-state
  oppositionReportedSentence
  true refl
  false refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Search intent for the exact first live residual.
------------------------------------------------------------------------

currentPrimaryArtifactSearchIntent : Search.SearchIntent
currentPrimaryArtifactSearchIntent = Search.searchIntent
  "SolomonIslandsForeignInterferenceSourceLegalWeldExact.currentSourceLegalResidual"
  "authenticate the primary artifact underlying the Opposition-attributed defeat-motion sentence"
  Search.propositionSourceProducer
  Search.exploitKnownResidual
  "Solomon Islands / Australia bilateral political communication"
  "late August to 6 September 2026, centred on the no-confidence motion and treaty negotiations"
  Search.primaryTextRequired
  "same communication chain as any message relied upon for the defeat-motion attribution"
  "ABC-authenticated Roach treaty/funding message and Opposition-published subsequent-message allegation"
  "primary artifact must preserve sender, recipient, timestamp, adjacency/context and content"
  "exclude republications, paraphrases and secondary stories as substitutes for the underlying artifact"
  (Search.searchBudget 6 10 3 "narrow acquisition budget: primary artifact first; stop when same-object provenance is paid")
  "Solomon defeat-motion primary-artifact acquisition intent"

currentProducerIsPropositionSourceProducer :
  Search.producerClass currentPrimaryArtifactSearchIntent ≡ Search.propositionSourceProducer
currentProducerIsPropositionSourceProducer = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RepeatedSecondaryReportPaysPrimaryArtifactDemand : Set where
data OppositionPublicationAuthenticatesUnderlyingArtifact : Set where
data PrimaryArtifactAcquisitionProvesAustralianSender : Set where
data SenderIdentityAutomaticallyProvesCoercion : Set where

secondaryRepetitionDoesNotPayPrimaryArtifact :
  RepeatedSecondaryReportPaysPrimaryArtifactDemand → ⊥
secondaryRepetitionDoesNotPayPrimaryArtifact ()

oppositionPublicationDoesNotAuthenticateArtifact :
  OppositionPublicationAuthenticatesUnderlyingArtifact → ⊥
oppositionPublicationDoesNotAuthenticateArtifact ()

acquisitionDoesNotProveSenderByExistence :
  PrimaryArtifactAcquisitionProvesAustralianSender → ⊥
acquisitionDoesNotProveSenderByExistence ()

senderIdentityDoesNotAutoEstablishCoercion :
  SenderIdentityAutomaticallyProvesCoercion → ⊥
senderIdentityDoesNotAutoEstablishCoercion ()

------------------------------------------------------------------------
-- Current residual remains exactly the one selected by the source/legal weld.
------------------------------------------------------------------------

currentResidualReference : String
currentResidualReference = Weld.nextExactProducer Weld.currentSourceLegalResidual
