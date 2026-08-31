module DASHI.Governance.SafeJustQualifiedClaimPromotionExact where

open import DASHI.Core.Prelude
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast
import DASHI.Governance.SafeJustForecastConsumerAdequacyExact as Adequacy
import DASHI.Governance.SafeJustEpistemicResidualLedgerExact as Residual
import DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact as Routing
import DASHI.Governance.SafeJustSituatedClaimAuthorityBridgeExact as SituatedBridge

------------------------------------------------------------------------
-- QUALIFIED PROMOTION: EVIDENCE PACKAGE + OPEN RESIDUAL LEDGER
--                       + SITUATED RESEARCH-USE AUTHORITY
--
-- Domain-owned #625 specialization of the generic QualifiedPromotion direction
-- identified on #620.  Promotion is allowed only for a declared consumer/claim
-- role, must retain unresolved epistemic obligations, and now carries the
-- upstream agenda/category/provenance/protocol/permission/obligation receipts
-- required by `SituatedClaimAuthoritySystemExact` for the Fanning forecast
-- evidence it consumes.  It is NOT closure, causal identification or mandate.
------------------------------------------------------------------------

record QualifiedSynthesisPromotion : Set₁ where
  constructor qualifiedSynthesisPromotion
  field
    projectionReceipt : Forecast.BAUProjectionReceipt
    forecastAdequacy : Adequacy.AdequateFor projectionReceipt Adequacy.forecastConsumer
    situatedForecastResearchUse :
      Situated.QualifiedUse
        SituatedBridge.safeJustSituatedClaimAuthoritySystem
        SituatedBridge.safeJustResearchAgenda
        SituatedBridge.safeJustIndicatorCategory
        SituatedBridge.fanningBAUProjectionClaim
        SituatedBridge.repositorySourceRegistryContext
        SituatedBridge.forecastResearchConsumer
        SituatedBridge.researchSynthesisUse
        SituatedBridge.attributionAndResidualCarriage
    claimRoute : Routing.ClaimRoute
    routeIsSynthesis : Routing.role claimRoute ≡ Routing.empiricalSynthesis
    blueWaterResidual :
      Residual.Carries Residual.kallisSynthesisStage Residual.missingNationalBlueWaterSeries
    projectionResidual :
      Residual.Carries Residual.kallisSynthesisStage Residual.projectionIsNotObservation
    uncertaintyResidual :
      Residual.Carries Residual.kallisSynthesisStage Residual.predictionIntervalUncertainty

open QualifiedSynthesisPromotion public

canonicalQualifiedSynthesisPromotion : QualifiedSynthesisPromotion
canonicalQualifiedSynthesisPromotion =
  qualifiedSynthesisPromotion
    Forecast.canonicalProjectionReceipt
    Adequacy.forecastAdequate
    SituatedBridge.fanningQualifiedResearchUse
    Routing.canonicalKallisSynthesisRoute
    refl
    Residual.blueWaterResidualStillOpenAtSynthesis
    Residual.projectionStatusStillOpenAtSynthesis
    Residual.synthesisProjectionUncertainty

qualifiedPromotionStillHasBlueWaterResidual :
  Residual.Carries Residual.kallisSynthesisStage Residual.missingNationalBlueWaterSeries
qualifiedPromotionStillHasBlueWaterResidual =
  blueWaterResidual canonicalQualifiedSynthesisPromotion

qualifiedPromotionStillHasProjectionResidual :
  Residual.Carries Residual.kallisSynthesisStage Residual.projectionIsNotObservation
qualifiedPromotionStillHasProjectionResidual =
  projectionResidual canonicalQualifiedSynthesisPromotion

qualifiedPromotionCarriesSituatedResearchUse :
  Situated.QualifiedUse
    SituatedBridge.safeJustSituatedClaimAuthoritySystem
    SituatedBridge.safeJustResearchAgenda
    SituatedBridge.safeJustIndicatorCategory
    SituatedBridge.fanningBAUProjectionClaim
    SituatedBridge.repositorySourceRegistryContext
    SituatedBridge.forecastResearchConsumer
    SituatedBridge.researchSynthesisUse
    SituatedBridge.attributionAndResidualCarriage
qualifiedPromotionCarriesSituatedResearchUse =
  situatedForecastResearchUse canonicalQualifiedSynthesisPromotion

qualifiedPromotionDoesNotBecomeCausal :
  Adequacy.AdequateFor
    Forecast.canonicalProjectionReceipt
    Adequacy.causalMechanismConsumer → ⊥
qualifiedPromotionDoesNotBecomeCausal = Adequacy.forecastNotCausalAuthority

qualifiedPromotionDoesNotBecomeNormative :
  Adequacy.AdequateFor
    Forecast.canonicalProjectionReceipt
    Adequacy.normativePolicyConsumer → ⊥
qualifiedPromotionDoesNotBecomeNormative = Adequacy.forecastNotNormativePolicyAuthority

qualifiedPromotionDoesNotCreateInterventionDecisionAuthority :
  SituatedBridge.DecisionAuthorized
    SituatedBridge.repositorySourceRegistryContext
    SituatedBridge.fanningBAUProjectionClaim
    SituatedBridge.policyInterventionUse → ⊥
qualifiedPromotionDoesNotCreateInterventionDecisionAuthority =
  SituatedBridge.fanningResearchUseDoesNotCreateDecisionAuthority

record QualifiedPromotionBoundary : Set where
  constructor qualifiedPromotionBoundary
  field
    promotionRequiresDeclaredConsumerAdequacy : Bool
    promotionRequiresDeclaredConsumerAdequacyIsTrue :
      promotionRequiresDeclaredConsumerAdequacy ≡ true
    promotionRequiresTypedClaimRoute : Bool
    promotionRequiresTypedClaimRouteIsTrue :
      promotionRequiresTypedClaimRoute ≡ true
    promotionRequiresSituatedResearchUse : Bool
    promotionRequiresSituatedResearchUseIsTrue :
      promotionRequiresSituatedResearchUse ≡ true
    promotionSilentlyDischargesResidualLedger : Bool
    promotionSilentlyDischargesResidualLedgerIsFalse :
      promotionSilentlyDischargesResidualLedger ≡ false
    qualifiedSynthesisIsCausalIdentification : Bool
    qualifiedSynthesisIsCausalIdentificationIsFalse :
      qualifiedSynthesisIsCausalIdentification ≡ false
    qualifiedSynthesisIsNormativeMandate : Bool
    qualifiedSynthesisIsNormativeMandateIsFalse :
      qualifiedSynthesisIsNormativeMandate ≡ false
    qualifiedResearchUseCreatesDecisionAuthority : Bool
    qualifiedResearchUseCreatesDecisionAuthorityIsFalse :
      qualifiedResearchUseCreatesDecisionAuthority ≡ false

canonicalQualifiedPromotionBoundary : QualifiedPromotionBoundary
canonicalQualifiedPromotionBoundary =
  qualifiedPromotionBoundary
    true refl true refl true refl false refl false refl false refl false refl
