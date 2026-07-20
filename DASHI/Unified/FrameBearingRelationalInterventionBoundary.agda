module DASHI.Unified.FrameBearingRelationalInterventionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Dynamics.EvidenceGatedRechartBoundary as Rechart
import DASHI.Dynamics.MaterialFeedbackInterventionReceipt as Intervention
import DASHI.Foundations.ObserverExtensionBoundary as Observer
import DASHI.Promotion.MetacognitiveFrameBearingState as Meta
import DASHI.Promotion.PluralSituatedHypothesisBoundary as Hypotheses
import DASHI.Sheaf.RelationalCompressionReceipt as Compression

data PipelineStage : Set where
  experienceStage frameStage hypothesisStage compressionStage : PipelineStage
  interventionStage observationStage revisionStage : PipelineStage

nextPipelineStage : PipelineStage → PipelineStage
nextPipelineStage experienceStage = frameStage
nextPipelineStage frameStage = hypothesisStage
nextPipelineStage hypothesisStage = compressionStage
nextPipelineStage compressionStage = interventionStage
nextPipelineStage interventionStage = observationStage
nextPipelineStage observationStage = revisionStage
nextPipelineStage revisionStage = revisionStage

experienceMovesToFrame : nextPipelineStage experienceStage ≡ frameStage
experienceMovesToFrame = refl

observationMovesToRevision : nextPipelineStage observationStage ≡ revisionStage
observationMovesToRevision = refl

record FrameBearingRelationalMachine : Set₁ where
  field
    Experience Frame Provenance Residual HypothesisCarrier Action Outcome : Set
    currentExperience : Experience
    observeFrame : Experience → Frame
    frameProvenance : Experience → Provenance
    initialResidual : Experience → Residual
    generateHypotheses : Experience → Frame → Residual → List HypothesisCarrier
    compressRelations : Experience → Frame → List HypothesisCarrier → Residual
    candidateAction : List HypothesisCarrier → Residual → Action
    validateAction : Action → Set
    applyAction : Experience → Action → Outcome
    observeResidual : Outcome → Residual
    rechartEvidence : Residual → Rechart.RechartEvidence
    interventionAuthority : Action → Set
    revisionLaw : Set

record IntegratedFrameBoundary : Set where
  constructor integratedFrameBoundary
  field
    metacognitiveBoundary : Meta.MetacognitivePowerUpBoundary
    pluralHypothesisBoundary : Hypotheses.PluralHypothesisBoundary
    relationalCompressionBoundary : Compression.RelationalCompressionBoundary
    materialInterventionBoundary : Intervention.MaterialInterventionBoundary
    observerBoundary : Observer.ObserverExtensionBoundary
    rechartBoundary : Rechart.EvidenceGatedRechartBoundary
    experiencePreservedAcrossFrameShift residualPreservedAcrossCompression : Bool
    hypothesesRemainPluralUntilTested interventionRequiresValidation outcomeFeedsRevision : Bool
    oneFrameExplainsEverything : Bool
    oneFrameExplainsEverythingIsFalse : oneFrameExplainsEverything ≡ false
    observerAutomaticallyHasLeverage : Bool
    observerAutomaticallyHasLeverageIsFalse : observerAutomaticallyHasLeverage ≡ false
    interpretation : String

canonicalIntegratedFrameBoundary : IntegratedFrameBoundary
canonicalIntegratedFrameBoundary =
  integratedFrameBoundary
    Meta.canonicalMetacognitivePowerUpBoundary
    Hypotheses.canonicalPluralHypothesisBoundary
    Compression.canonicalRelationalCompressionBoundary
    Intervention.canonicalMaterialInterventionBoundary
    Observer.canonicalObserverExtensionBoundary
    Rechart.canonicalEvidenceGatedRechartBoundary
    true true true true true
    false refl
    false refl
    "experience is preserved while its frame is exposed; hypotheses remain plural, compression retains remainder, intervention requires validation, and outcomes feed revision"
