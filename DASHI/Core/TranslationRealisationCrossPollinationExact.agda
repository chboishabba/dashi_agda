module DASHI.Core.TranslationRealisationCrossPollinationExact where

------------------------------------------------------------------------
-- CROSS-PR TRANSLATION / REALISATION ADEQUACY CAPSTONE
--
-- Internal theorem-pattern provenance only:
--   #615 historical source recovery
--   #621 consumer-relative transfer + realization authority
--   #625 provisioning mediation / observed residual != causal identification
--   #608 observer-contract guarded reification
--   #602 semantic authority != physical execution work
--
-- No draft code is imported.  This module records the shared generic structure
-- so those branches can later become thin adapters after ancestry reconciliation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedTranslationRealisationExact as Adequacy
import DASHI.Core.ResidualObligationPropagationExact as Residual

------------------------------------------------------------------------
-- Consumer-indexed adequacy matrix.
------------------------------------------------------------------------

data AuditConsumer : Set where
  historicalConsumer
  executionConsumer
  empiricalConsumer
  normativeConsumer
  : AuditConsumer

data AuditEvidence : Adequacy.AdequacyStage → AuditConsumer → Set where
  sourceForHistory : AuditEvidence Adequacy.sourceAcquired historicalConsumer
  translationForHistory : AuditEvidence Adequacy.translated historicalConsumer
  reconstructionForHistory : AuditEvidence Adequacy.reconstructed historicalConsumer
  realizationForExecution : AuditEvidence Adequacy.realized executionConsumer
  kernelForExecution : AuditEvidence Adequacy.kernelChecked executionConsumer
  empiricalForEmpirical : AuditEvidence Adequacy.empiricallyCalibrated empiricalConsumer
  normativeForNormative : AuditEvidence Adequacy.normativelyAdmitted normativeConsumer

canonicalAuditMatrix : Adequacy.StageConsumerAdequacy AuditConsumer
canonicalAuditMatrix = Adequacy.stageConsumerAdequacy AuditEvidence

translatedHistoricalDoesNotMeanExecutionAdequate :
  AuditEvidence Adequacy.translated historicalConsumer →
  AuditEvidence Adequacy.translated executionConsumer → ⊥
translatedHistoricalDoesNotMeanExecutionAdequate _ ()

kernelExecutionDoesNotMeanEmpiricalAdequate :
  AuditEvidence Adequacy.kernelChecked executionConsumer →
  AuditEvidence Adequacy.kernelChecked empiricalConsumer → ⊥
kernelExecutionDoesNotMeanEmpiricalAdequate _ ()

empiricalAdequacyDoesNotMeanNormativeAdmission :
  AuditEvidence Adequacy.empiricallyCalibrated empiricalConsumer →
  AuditEvidence Adequacy.empiricallyCalibrated normativeConsumer → ⊥
empiricalAdequacyDoesNotMeanNormativeAdmission _ ()

------------------------------------------------------------------------
-- Generic unresolved bridge remains live after formal translation and theorem
-- production; it cannot be erased merely by reaching a downstream stage.
------------------------------------------------------------------------

semanticBridgeStillLiveAfterTranslation :
  Residual.carries Residual.demoFlow Residual.translationStage Residual.missingSemanticBridge
semanticBridgeStillLiveAfterTranslation = Residual.atTranslation

semanticBridgeStillLiveAtTheorem :
  Residual.carries Residual.demoFlow Residual.theoremStage Residual.missingSemanticBridge
semanticBridgeStillLiveAtTheorem = Residual.atTheorem

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    historicalRecoveryImpliesExecutableSemantics : Bool
    historicalRecoveryImpliesExecutableSemanticsIsFalse :
      historicalRecoveryImpliesExecutableSemantics ≡ false
    structuralFitImpliesUniversalConsumerFitness : Bool
    structuralFitImpliesUniversalConsumerFitnessIsFalse :
      structuralFitImpliesUniversalConsumerFitness ≡ false
    observedOutcomeImpliesCausalMechanism : Bool
    observedOutcomeImpliesCausalMechanismIsFalse :
      observedOutcomeImpliesCausalMechanism ≡ false
    observerReceiptImpliesObserverContract : Bool
    observerReceiptImpliesObserverContractIsFalse :
      observerReceiptImpliesObserverContract ≡ false
    semanticAuthorityImpliesEfficientExecution : Bool
    semanticAuthorityImpliesEfficientExecutionIsFalse :
      semanticAuthorityImpliesEfficientExecution ≡ false
    downstreamTheoremErasesUnresolvedBridge : Bool
    downstreamTheoremErasesUnresolvedBridgeIsFalse :
      downstreamTheoremErasesUnresolvedBridge ≡ false

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl false refl false refl false refl
