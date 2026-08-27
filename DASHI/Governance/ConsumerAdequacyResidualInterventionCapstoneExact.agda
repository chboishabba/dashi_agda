module DASHI.Governance.ConsumerAdequacyResidualInterventionCapstoneExact where

------------------------------------------------------------------------
-- CONSUMER ADEQUACY / RESIDUAL / INTERVENTION CAPSTONE
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedTranslationRealisationExact as Adequacy
import DASHI.Core.ResidualObligationPropagationExact as Residual
import DASHI.Core.TranslationRealisationCrossPollinationExact as Cross
import DASHI.Governance.InterventionMechanismDecompositionExact as Intervention

adequateForStructuralNotEmpirical :
  Adequacy.ConsumerRelativeAdequacyWitness
    Adequacy.demoSystem
    Adequacy.sourceText
    Adequacy.structuralConsumer
    Adequacy.empiricalConsumer
adequateForStructuralNotEmpirical = Adequacy.demoConsumerRelative

residualSurvivesTranslation :
  Residual.carries Residual.demoFlow Residual.translationStage Residual.missingSemanticBridge
residualSurvivesTranslation = Cross.semanticBridgeStillLiveAfterTranslation

residualSurvivesTheoremProduction :
  Residual.carries Residual.demoFlow Residual.theoremStage Residual.missingSemanticBridge
residualSurvivesTheoremProduction = Cross.semanticBridgeStillLiveAtTheorem

resourceOnlyDoesNotExpandCapability :
  Intervention.ResourceRepair Intervention.demoMechanisms Intervention.resourceOnly →
  Intervention.CapabilityExpanded Intervention.demoMechanisms Intervention.resourceOnly → ⊥
resourceOnlyDoesNotExpandCapability = Intervention.resourceRepairAloneDoesNotGiveCapability

institutionOnlyDoesNotExpandCapability :
  Intervention.InstitutionalRepair Intervention.demoMechanisms Intervention.recognitionOnly →
  Intervention.CapabilityExpanded Intervention.demoMechanisms Intervention.recognitionOnly → ⊥
institutionOnlyDoesNotExpandCapability =
  Intervention.institutionalRepairAloneDoesNotGiveCapability

record ConsumerAdequacyResidualInterventionBoundary : Set where
  constructor consumerAdequacyResidualInterventionBoundary
  field
    validArrowMeansUniversalArrow : Bool
    validArrowMeansUniversalArrowIsFalse : validArrowMeansUniversalArrow ≡ false
    promotionErasesResidual : Bool
    promotionErasesResidualIsFalse : promotionErasesResidual ≡ false
    oneRepairCoordinateMeansGlobalRepair : Bool
    oneRepairCoordinateMeansGlobalRepairIsFalse :
      oneRepairCoordinateMeansGlobalRepair ≡ false
    kernelSuccessMeansEmpiricalSuccess : Bool
    kernelSuccessMeansEmpiricalSuccessIsFalse :
      kernelSuccessMeansEmpiricalSuccess ≡ false
    empiricalSuccessMeansNormativeAdmission : Bool
    empiricalSuccessMeansNormativeAdmissionIsFalse :
      empiricalSuccessMeansNormativeAdmission ≡ false

canonicalConsumerAdequacyResidualInterventionBoundary :
  ConsumerAdequacyResidualInterventionBoundary
canonicalConsumerAdequacyResidualInterventionBoundary =
  consumerAdequacyResidualInterventionBoundary
    false refl false refl false refl false refl false refl
