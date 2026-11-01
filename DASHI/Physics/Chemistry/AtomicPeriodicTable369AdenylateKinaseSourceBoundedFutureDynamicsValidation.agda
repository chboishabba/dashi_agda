module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedFutureDynamicsValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceBoundedFutureDynamicsExact as D

sourceBoundedDynamicsRegression :
  D.AdKSourceBoundedFutureDynamicsBoundary.nontrivialSourceGraphActionsRetained
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ true
  × D.AdKSourceBoundedFutureDynamicsBoundary.onlyOwnedRouteEdgesAdmitted
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ true
  × D.AdKSourceBoundedFutureDynamicsBoundary.thirdAxisConsumerDynamicallySafeUnderGraphMoves
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ true
sourceBoundedDynamicsRegression = refl , refl , refl

attributionRegression :
  D.AdKSourceBoundedFutureDynamicsBoundary.routeGraphEqualsExperimentalKinetics
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ false
  × D.AdKSourceBoundedFutureDynamicsBoundary.pathFluxEqualsPerEdgeRate
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ false
  × D.AdKSourceBoundedFutureDynamicsBoundary.computationalRouteSourcePaysDASHIDynamicSafetyTheorem
    D.canonicalAdKSourceBoundedFutureDynamicsBoundary
  ≡ false
attributionRegression = refl , refl , refl
