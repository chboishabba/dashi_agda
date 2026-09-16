module DASHI.Core.ConsumerSafeRefinementPromotionValidation where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerSafeRefinementPromotionExact as P

------------------------------------------------------------------------
-- RED/GREEN validation root for the generic promotion theorem.
------------------------------------------------------------------------

boundaryRegression :
  P.ConsumerSafeRefinementPromotionBoundary.counterexampleExcludesCoarseEligibility
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ true
  × P.ConsumerSafeRefinementPromotionBoundary.localRepairConstructsFineEligibility
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ true
  × P.ConsumerSafeRefinementPromotionBoundary.paretoSelectionRequiresEligibility
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ true
boundaryRegression = refl , refl , refl

attributionRegression :
  P.ConsumerSafeRefinementPromotionBoundary.domainSourceBecomesAuthorOfGenericTheorem
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ false
  × P.ConsumerSafeRefinementPromotionBoundary.genericPromotionCreatesEmpiricalTruth
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ false
  × P.ConsumerSafeRefinementPromotionBoundary.consumerSafeMeansWorldComplete
    P.canonicalConsumerSafeRefinementPromotionBoundary
  ≡ false
attributionRegression = refl , refl , refl
