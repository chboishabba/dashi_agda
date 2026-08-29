module DASHI.Programmes.RTXLightTransportRefinementExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- dashiRTX literal light-transport refinement socket.
--
-- Quadtree / ultrametric / MDL refinement is only useful for a declared
-- downstream observation when that refinement preserves the observation that
-- the consumer actually uses.  This is deliberately weaker than claiming that
-- lower rendering error or lower description length establishes physical truth.
------------------------------------------------------------------------

record LightTransportRefinementInterface : Set₁ where
  constructor lightTransportRefinementInterface
  field
    State Observation : Set
    refine : State → State
    observe : State → Observation
    refinementPreservesObservation :
      ∀ state → observe (refine state) ≡ observe state

open LightTransportRefinementInterface public

refineN :
  (r : LightTransportRefinementInterface) →
  Nat → State r → State r
refineN r zero state = state
refineN r (suc n) state = refine r (refineN r n state)

iteratedRefinementPreservesObservation :
  (r : LightTransportRefinementInterface) →
  ∀ n state →
  observe r (refineN r n state) ≡ observe r state
iteratedRefinementPreservesObservation r zero state = refl
iteratedRefinementPreservesObservation r (suc n) state =
  trans
    (refinementPreservesObservation r (refineN r n state))
    (iteratedRefinementPreservesObservation r n state)

------------------------------------------------------------------------
-- Claim boundary for the renderer/MDL lane.
------------------------------------------------------------------------

record RTXRefinementBoundary : Set where
  constructor rtxRefinementBoundary
  field
    lowerMDLIsPhysicalTruth : Bool
    lowerMDLIsPhysicalTruthIsFalse : lowerMDLIsPhysicalTruth ≡ false

    observationPreservingRefinementIsReusableByConsumer : Bool
    observationPreservingRefinementIsReusableByConsumerIsTrue :
      observationPreservingRefinementIsReusableByConsumer ≡ true

canonicalRTXRefinementBoundary : RTXRefinementBoundary
canonicalRTXRefinementBoundary =
  rtxRefinementBoundary
    false refl
    true refl
