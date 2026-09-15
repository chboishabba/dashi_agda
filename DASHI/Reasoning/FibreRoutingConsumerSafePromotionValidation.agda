module DASHI.Reasoning.FibreRoutingConsumerSafePromotionValidation where

open import DASHI.Core.Prelude

import DASHI.Reasoning.FibreRoutingConsumerSafePromotionExact as P

promotionRegression :
  P.FibreRoutingConsumerSafePromotionBoundary.genericPromotionInstantiatedForOverlapRepair
    P.canonicalFibreRoutingConsumerSafePromotionBoundary
  ≡ true
  × P.FibreRoutingConsumerSafePromotionBoundary.hardWinnerExcludedForOverlapConsumer
    P.canonicalFibreRoutingConsumerSafePromotionBoundary
  ≡ true
  × P.FibreRoutingConsumerSafePromotionBoundary.softOverlapParetoSelected
    P.canonicalFibreRoutingConsumerSafePromotionBoundary
  ≡ true
promotionRegression = refl , refl , refl

attributionRegression :
  P.FibreRoutingConsumerSafePromotionBoundary.domainDonorBecomesAuthorOfGenericPromotion
    P.canonicalFibreRoutingConsumerSafePromotionBoundary
  ≡ false
  × P.FibreRoutingConsumerSafePromotionBoundary.genericPromotionCreatesBiologicalMechanism
    P.canonicalFibreRoutingConsumerSafePromotionBoundary
  ≡ false
attributionRegression = refl , refl
