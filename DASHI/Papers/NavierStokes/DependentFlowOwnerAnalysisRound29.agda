module DASHI.Papers.NavierStokes.DependentFlowOwnerAnalysisRound29 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoHighestAlphaRound29Exact as Round29

record DependentFlowOwnerAnalysisRound29Status : Set where
  constructor dependent-flow-owner-analysis-round29-status
  field
    reconstructedPhysicalSelectorProduced : Bool
    dependentPhysicalODECarrierProduced : Bool
    finiteCommutatorCoefficientIntegrated : Bool
    finiteEnergyContinuationBridgeIntegrated : Bool
    globalFiveSourcePairingProduced : Bool
    delayedPositivePartProduced : Bool
    multiplierTelescopingProduced : Bool
    crossShellScalarCoreProduced : Bool
    scaleNormalisedAmplitudeAuditProduced : Bool
    hhBadFeasibilityCriterionProduced : Bool
    symbolicOwnerOptimizationProduced : Bool
    boundaryClassificationProduced : Bool
    quantitativeCriticalToSerrinProduced : Bool

    fullNonlinearEquivarianceProduced : Bool
    finiteGlobalPhysicalFlowProduced : Bool
    physicalShellBalanceProduced : Bool
    cutoffUniformCotlarSteinProduced : Bool
    physicalNineOwnerEstimatesProduced : Bool
    strictViscosityMarginProduced : Bool
    continuumLimitsProduced : Bool
    unconditionalClayPromotion : Bool

open DependentFlowOwnerAnalysisRound29Status public

canonicalDependentFlowOwnerAnalysisRound29Status :
  DependentFlowOwnerAnalysisRound29Status
canonicalDependentFlowOwnerAnalysisRound29Status =
  dependent-flow-owner-analysis-round29-status
    true true true true true true true true true true true true true
    false false false false false false false false

finiteFlowArchitectureAdvanced :
  dependentPhysicalODECarrierProduced
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ true
finiteFlowArchitectureAdvanced = refl

signedTaxArchitectureAdvanced :
  delayedPositivePartProduced
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ true
signedTaxArchitectureAdvanced = refl

finiteGlobalFlowStillOpen :
  finiteGlobalPhysicalFlowProduced
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ false
finiteGlobalFlowStillOpen = refl

physicalTaxesStillOpen :
  physicalNineOwnerEstimatesProduced
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ false
physicalTaxesStillOpen = refl

strictMarginStillOpen :
  strictViscosityMarginProduced
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ false
strictMarginStillOpen = refl

clayPromotionStillFalse :
  unconditionalClayPromotion
    canonicalDependentFlowOwnerAnalysisRound29Status ≡ false
clayPromotionStillFalse = refl
