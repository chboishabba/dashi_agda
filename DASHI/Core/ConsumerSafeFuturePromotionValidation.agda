module DASHI.Core.ConsumerSafeFuturePromotionValidation where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerSafeFuturePromotionExact as P

------------------------------------------------------------------------
-- RED/GREEN validation root: static selection safety and future safety are
-- independent payments, joined only through an application realisation witness.
------------------------------------------------------------------------

compositionRegression :
  P.ConsumerSafeFuturePromotionBoundary.staticPromotionRetained
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ true
  × P.ConsumerSafeFuturePromotionBoundary.futureSafePromotionRetained
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ true
  × P.ConsumerSafeFuturePromotionBoundary.selectedModelRealisationRequired
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ true
compositionRegression = refl , refl , refl

nonPromotionRegression :
  P.ConsumerSafeFuturePromotionBoundary.staticConsumerSafetyAloneImpliesFutureSafety
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ false
  × P.ConsumerSafeFuturePromotionBoundary.futureSafetyAloneImpliesParetoSelection
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ false
  × P.ConsumerSafeFuturePromotionBoundary.crossDomainReuseTransfersAuthorship
    P.canonicalConsumerSafeFuturePromotionBoundary
  ≡ false
nonPromotionRegression = refl , refl , refl
