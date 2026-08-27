module DASHI.Governance.SafeJustQualifiedClaimPromotionExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast
import DASHI.Governance.SafeJustForecastConsumerAdequacyExact as Adequacy
import DASHI.Governance.SafeJustEpistemicResidualLedgerExact as Residual
import DASHI.Governance.Kallis2025ClaimAuthorityRoutingExact as Routing

------------------------------------------------------------------------
-- QUALIFIED PROMOTION: EVIDENCE PACKAGE + OPEN RESIDUAL LEDGER
--
-- Domain-owned #625 specialization of the generic QualifiedPromotion direction
-- identified on #620.  Promotion is allowed only for a declared consumer/claim
-- role and must retain unresolved epistemic obligations.  It is NOT closure.
------------------------------------------------------------------------

record QualifiedSynthesisPromotion : Set₁ where
  constructor qualifiedSynthesisPromotion
  field
    projectionReceipt : Forecast.BAUProjectionReceipt
    forecastAdequacy : Adequacy.AdequateFor projectionReceipt Adequacy.forecastConsumer
    claimRoute : Routing.ClaimRoute
    routeIsSynthesis : Routing.ClaimRoute.role claimRoute ≡ Routing.empiricalSynthesis
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

record QualifiedPromotionBoundary : Set where
  constructor qualifiedPromotionBoundary
  field
    promotionRequiresDeclaredConsumerAdequacy : Bool
    promotionRequiresDeclaredConsumerAdequacyIsTrue :
      promotionRequiresDeclaredConsumerAdequacy ≡ true
    promotionRequiresTypedClaimRoute : Bool
    promotionRequiresTypedClaimRouteIsTrue :
      promotionRequiresTypedClaimRoute ≡ true
    promotionSilentlyDischargesResidualLedger : Bool
    promotionSilentlyDischargesResidualLedgerIsFalse :
      promotionSilentlyDischargesResidualLedger ≡ false
    qualifiedSynthesisIsCausalIdentification : Bool
    qualifiedSynthesisIsCausalIdentificationIsFalse :
      qualifiedSynthesisIsCausalIdentification ≡ false
    qualifiedSynthesisIsNormativeMandate : Bool
    qualifiedSynthesisIsNormativeMandateIsFalse :
      qualifiedSynthesisIsNormativeMandate ≡ false

canonicalQualifiedPromotionBoundary : QualifiedPromotionBoundary
canonicalQualifiedPromotionBoundary =
  qualifiedPromotionBoundary true refl true refl false refl false refl false refl
