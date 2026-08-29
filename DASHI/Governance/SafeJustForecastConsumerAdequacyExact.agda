module DASHI.Governance.SafeJustForecastConsumerAdequacyExact where

open import DASHI.Core.Prelude
import DASHI.Governance.Fanning2022ForecastAuthorityExact as Forecast

------------------------------------------------------------------------
-- FANNING FORECAST RECEIPT: CONSUMER-INDEXED ADEQUACY
--
-- Thin #625 specialization of the consumer-indexed adequacy theorem pattern
-- developed independently on draft PR #620.  No cross-draft import is used.
------------------------------------------------------------------------

data ForecastConsumer : Set where
  forecastConsumer
  causalMechanismConsumer
  observedFutureConsumer
  normativePolicyConsumer
  : ForecastConsumer

data AdequateFor : Forecast.BAUProjectionReceipt → ForecastConsumer → Set where
  canonicalForecastAdequate :
    AdequateFor Forecast.canonicalProjectionReceipt forecastConsumer

forecastAdequate :
  AdequateFor Forecast.canonicalProjectionReceipt forecastConsumer
forecastAdequate = canonicalForecastAdequate

forecastNotCausalAuthority :
  AdequateFor Forecast.canonicalProjectionReceipt causalMechanismConsumer → ⊥
forecastNotCausalAuthority ()

forecastNotObservedFutureAuthority :
  AdequateFor Forecast.canonicalProjectionReceipt observedFutureConsumer → ⊥
forecastNotObservedFutureAuthority ()

forecastNotNormativePolicyAuthority :
  AdequateFor Forecast.canonicalProjectionReceipt normativePolicyConsumer → ⊥
forecastNotNormativePolicyAuthority ()

record ForecastConsumerSeparation : Set₁ where
  constructor forecastConsumerSeparation
  field
    forecastUse :
      AdequateFor Forecast.canonicalProjectionReceipt forecastConsumer
    causalUseFails :
      AdequateFor Forecast.canonicalProjectionReceipt causalMechanismConsumer → ⊥
    observedFutureUseFails :
      AdequateFor Forecast.canonicalProjectionReceipt observedFutureConsumer → ⊥
    normativePolicyUseFails :
      AdequateFor Forecast.canonicalProjectionReceipt normativePolicyConsumer → ⊥

canonicalForecastConsumerSeparation : ForecastConsumerSeparation
canonicalForecastConsumerSeparation =
  forecastConsumerSeparation
    forecastAdequate
    forecastNotCausalAuthority
    forecastNotObservedFutureAuthority
    forecastNotNormativePolicyAuthority

record ForecastConsumerAdequacyBoundary : Set where
  constructor forecastConsumerAdequacyBoundary
  field
    adequateForecastImpliesCausalMechanism : Bool
    adequateForecastImpliesCausalMechanismIsFalse :
      adequateForecastImpliesCausalMechanism ≡ false
    adequateForecastImpliesObservedFuture : Bool
    adequateForecastImpliesObservedFutureIsFalse :
      adequateForecastImpliesObservedFuture ≡ false
    adequateForecastImpliesNormativePolicyAuthority : Bool
    adequateForecastImpliesNormativePolicyAuthorityIsFalse :
      adequateForecastImpliesNormativePolicyAuthority ≡ false
    consumerAdequacyIsUniversalPropertyOfReceipt : Bool
    consumerAdequacyIsUniversalPropertyOfReceiptIsFalse :
      consumerAdequacyIsUniversalPropertyOfReceipt ≡ false

canonicalForecastConsumerAdequacyBoundary : ForecastConsumerAdequacyBoundary
canonicalForecastConsumerAdequacyBoundary =
  forecastConsumerAdequacyBoundary false refl false refl false refl false refl
