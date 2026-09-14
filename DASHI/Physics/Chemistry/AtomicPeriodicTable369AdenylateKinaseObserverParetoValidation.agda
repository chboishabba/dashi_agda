module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseObserverParetoExact as P

------------------------------------------------------------------------
-- RED/GREEN validation root: observer richness is consumer-indexed and
-- eligible-before-minimal, not "more axes always wins".
------------------------------------------------------------------------

twoAxisSelectionRegression :
  P.AdKObserverParetoBoundary.joinedTwoIsMinimalEligibleForTwoAxisConsumer
    P.canonicalAdKObserverParetoBoundary
  ≡ true
  × P.AdKObserverParetoBoundary.threeAxisAutomaticallyPreferredForTwoAxisConsumer
    P.canonicalAdKObserverParetoBoundary
  ≡ false
twoAxisSelectionRegression = refl , refl

thirdAxisSelectionRegression :
  P.AdKObserverParetoBoundary.twoAxisJoinEligibleForThirdAxisConsumer
    P.canonicalAdKObserverParetoBoundary
  ≡ false
  × P.AdKObserverParetoBoundary.threeAxisIsMinimalEligibleForThirdAxisConsumer
    P.canonicalAdKObserverParetoBoundary
  ≡ true
thirdAxisSelectionRegression = refl , refl

promotionRegression :
  P.AdKObserverParetoBoundary.shorterObserverMeansPhysicalTruth
    P.canonicalAdKObserverParetoBoundary
  ≡ false
  × P.AdKObserverParetoBoundary.moreAxesImproveEveryConsumer
    P.canonicalAdKObserverParetoBoundary
  ≡ false
promotionRegression = refl , refl
