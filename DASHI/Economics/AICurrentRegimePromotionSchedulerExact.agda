module DASHI.Economics.AICurrentRegimePromotionSchedulerExact where

open import DASHI.Core.Prelude

import DASHI.Economics.SourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Economics.AICurrentRegimeCalibration2026Exact as Current
import DASHI.Economics.AICurrentRegimeSourceAttributionCrossPollinationExact as SourceBoundary
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal

------------------------------------------------------------------------
-- BIDI PROMOTION SCHEDULER FOR CURRENT-REGIME CLAIMS
--
-- Stronger claims reverse-map to the producer still needed after the available
-- source proposition.  This prevents a source-closed coordinate from being
-- confused with conclusion closure.
------------------------------------------------------------------------

data CurrentRegimeClaim : Set where
  microsoftIncrementalAIGrossMarginKnown
  microsoftIncrementalAIUnitEconomicsPositive
  nvidiaCoreWeaveDollarRevenueCircularityQuantified
  nvidiaCoreWeaveTerminalDemandIndependent
  coreWeaveFacilitiesAreClassicalCDO
  coreWeavePortfolioRiskIndependent
  softBankOpenAIValuationGainIsExternalCash
  softBankOpenAIInvestmentEconomicallyValidated
  tsmcPermanentManufacturingChokepoint
  tsmcScarcityRentQuantified
  chinaFivePercentChipShare
  moonshotOpenWeightReleaseCausedByServingScarcity
  chinaServingScarcityImpairsSubscriptionEconomics
  currentAIInfrastructureBubble
  currentAIInfrastructureFraud
  incrementalAIInfrastructureTerminallyValidated
  : CurrentRegimeClaim

data CurrentRegimeProducer : Set where
  aiSpecificSegmentMarginProducer
  aiUsefulWorkUnitEconomicsProducer
  capitalRevenueFlowTracingProducer
  terminalPayerPartitionProducer
  classicalCDOStructureProducer
  ultimateEconomicDriverIndependenceProducer
  externalCashRealisationProducer
  longHorizonExternalNPVProducer
  manufacturingSubstitutionCapacityProducer
  scarcityRentQuantificationProducer
  patronusChipSharePrimaryProducer
  moonshotCausalTimelineProducer
  subscriptionServingEconomicsProducer
  regimeClassificationProducer
  fraudEvidenceProducer
  terminalEconomicValidationProducer
  : CurrentRegimeProducer

requiredProducer : CurrentRegimeClaim → CurrentRegimeProducer
requiredProducer microsoftIncrementalAIGrossMarginKnown = aiSpecificSegmentMarginProducer
requiredProducer microsoftIncrementalAIUnitEconomicsPositive = aiUsefulWorkUnitEconomicsProducer
requiredProducer nvidiaCoreWeaveDollarRevenueCircularityQuantified = capitalRevenueFlowTracingProducer
requiredProducer nvidiaCoreWeaveTerminalDemandIndependent = terminalPayerPartitionProducer
requiredProducer coreWeaveFacilitiesAreClassicalCDO = classicalCDOStructureProducer
requiredProducer coreWeavePortfolioRiskIndependent = ultimateEconomicDriverIndependenceProducer
requiredProducer softBankOpenAIValuationGainIsExternalCash = externalCashRealisationProducer
requiredProducer softBankOpenAIInvestmentEconomicallyValidated = longHorizonExternalNPVProducer
requiredProducer tsmcPermanentManufacturingChokepoint = manufacturingSubstitutionCapacityProducer
requiredProducer tsmcScarcityRentQuantified = scarcityRentQuantificationProducer
requiredProducer chinaFivePercentChipShare = patronusChipSharePrimaryProducer
requiredProducer moonshotOpenWeightReleaseCausedByServingScarcity = moonshotCausalTimelineProducer
requiredProducer chinaServingScarcityImpairsSubscriptionEconomics = subscriptionServingEconomicsProducer
requiredProducer currentAIInfrastructureBubble = regimeClassificationProducer
requiredProducer currentAIInfrastructureFraud = fraudEvidenceProducer
requiredProducer incrementalAIInfrastructureTerminallyValidated = terminalEconomicValidationProducer

------------------------------------------------------------------------
-- Source closure and promotion closure are different coordinates.
------------------------------------------------------------------------

currentCalibration : Current.AICurrentRegimeCalibration2026
currentCalibration = Current.canonicalAICurrentRegimeCalibration2026

sourceAttributionBoundaryRetained : Attribution.SourceUseReceipt
sourceAttributionBoundaryRetained = SourceBoundary.microsoftEconomicUse

record PromotionResidual : Set where
  constructor promotionResidual
  field
    claim : CurrentRegimeClaim
    producer : CurrentRegimeProducer
    sourceLayerAvailable : Bool
    strongerPromotionClosed : Bool

open PromotionResidual public

microsoftIncrementalMarginResidual : PromotionResidual
microsoftIncrementalMarginResidual = promotionResidual
  microsoftIncrementalAIGrossMarginKnown aiSpecificSegmentMarginProducer true false

coreWeaveCDOResidual : PromotionResidual
coreWeaveCDOResidual = promotionResidual
  coreWeaveFacilitiesAreClassicalCDO classicalCDOStructureProducer true false

softBankValidationResidual : PromotionResidual
softBankValidationResidual = promotionResidual
  softBankOpenAIInvestmentEconomicallyValidated longHorizonExternalNPVProducer true false

chinaChipShareResidual : PromotionResidual
chinaChipShareResidual = promotionResidual
  chinaFivePercentChipShare patronusChipSharePrimaryProducer true false

bubbleResidual : PromotionResidual
bubbleResidual = promotionResidual
  currentAIInfrastructureBubble regimeClassificationProducer true false

terminalValidationResidual : PromotionResidual
terminalValidationResidual = promotionResidual
  incrementalAIInfrastructureTerminallyValidated terminalEconomicValidationProducer true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SourceClosureImpliesPromotionClosurePermission : Set where

data SameProducerKindPaysDifferentClaimPermission : Set where

data CurrentEvidenceBundleImpliesTerminalValidationPermission : Set where

sourceClosureDoesNotAutoPromoteToConclusionClosure :
  SourceClosureImpliesPromotionClosurePermission → ⊥
sourceClosureDoesNotAutoPromoteToConclusionClosure ()

producerKindDoesNotAutoPayDifferentClaim :
  SameProducerKindPaysDifferentClaimPermission → ⊥
producerKindDoesNotAutoPayDifferentClaim ()

currentEvidenceBundleDoesNotCloseTerminalValidation :
  CurrentEvidenceBundleImpliesTerminalValidationPermission → ⊥
currentEvidenceBundleDoesNotCloseTerminalValidation ()

sourceReceiptDoesNotPayPromotionStep :
  Attribution.SourceReceiptImpliesPromotionStepPermission → ⊥
sourceReceiptDoesNotPayPromotionStep =
  Attribution.sourceReceiptDoesNotAutoPromoteToPromotionStep

surroundingSignalsStillDoNotCloseTerminalValidation :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsStillDoNotCloseTerminalValidation =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation
