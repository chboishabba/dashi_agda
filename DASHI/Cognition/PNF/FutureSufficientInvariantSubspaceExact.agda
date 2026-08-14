module DASHI.Cognition.PNF.FutureSufficientInvariantSubspaceExact where

------------------------------------------------------------------------
-- FUTURE-SUFFICIENT INVARIANT REPRESENTATIONS
--
-- A representation is useful for a declared consumer only when two distinct
-- obligations are met:
--
--   (1) dynamics close in the latent carrier: E(F_a x) = M_a(E x);
--   (2) the consumer observation factors through E.
--
-- These two laws imply that equality of latent codes is preserved through every
-- finite action trace and therefore lies inside the canonical future-observation
-- equivalence.  This is the exact deterministic core of the proposed
-- "future-sufficient invariant observable subspace" idea; no vector-space or
-- spectral assumptions are needed for the theorem itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

record FutureSufficientInvariantRepresentation
    (State Action Observation Latent : Set) : Set₁ where
  constructor futureSufficientInvariantRepresentation
  field
    encode : State → Latent
    step : Action → State → State
    latentStep : Action → Latent → Latent
    observe : State → Observation
    decodeObservation : Latent → Observation
    actionLabel : Action → String

    -- Dynamical simplicity / invariant latent carrier.
    intertwines :
      (action : Action) (state : State) →
      encode (step action state) ≡ latentStep action (encode state)

    -- Consumer sufficiency at the present state.
    observationFactors :
      (state : State) →
      observe state ≡ decodeObservation (encode state)

open FutureSufficientInvariantRepresentation public

runLatent :
  ∀ {State Action Observation Latent} →
  FutureSufficientInvariantRepresentation State Action Observation Latent →
  List Action → Latent → Latent
runLatent representation [] latent = latent
runLatent representation (action ∷ actions) latent =
  runLatent representation actions (latentStep representation action latent)

runEncodingIntertwines :
  ∀ {State Action Observation Latent}
    (representation :
      FutureSufficientInvariantRepresentation State Action Observation Latent)
    (actions : List Action) (state : State) →
  encode representation
    (Refinement.run (step representation) actions state)
  ≡ runLatent representation actions (encode representation state)
runEncodingIntertwines representation [] state = refl
runEncodingIntertwines representation (action ∷ actions) state =
  trans
    (runEncodingIntertwines representation actions
      (step representation action state))
    (cong (runLatent representation actions)
      (intertwines representation action state))

latentEqualityPreservedByTrace :
  ∀ {State Action Observation Latent}
    (representation :
      FutureSufficientInvariantRepresentation State Action Observation Latent)
    (actions : List Action) {left right : State} →
  encode representation left ≡ encode representation right →
  runLatent representation actions (encode representation left)
  ≡ runLatent representation actions (encode representation right)
latentEqualityPreservedByTrace representation actions equality =
  cong (runLatent representation actions) equality

latentKernelImpliesTraceObservationEquality :
  ∀ {State Action Observation Latent}
    (representation :
      FutureSufficientInvariantRepresentation State Action Observation Latent)
    {left right : State} →
  encode representation left ≡ encode representation right →
  Bridge.TraceEquivalent
    (observe representation) (step representation) left right
latentKernelImpliesTraceObservationEquality representation codeEqual actions =
  trans
    (observationFactors representation
      (Refinement.run (step representation) actions _))
    (trans
      (cong (decodeObservation representation)
        (runEncodingIntertwines representation actions _))
      (trans
        (cong (decodeObservation representation)
          (latentEqualityPreservedByTrace representation actions codeEqual))
        (trans
          (cong (decodeObservation representation)
            (sym (runEncodingIntertwines representation actions _)))
          (sym (observationFactors representation
            (Refinement.run (step representation) actions _))))))

------------------------------------------------------------------------
-- MAIN THEOREM
--
-- ker(E) is contained in canonical future equivalence whenever the latent
-- dynamics close and the declared consumer observation factors through E.
------------------------------------------------------------------------

invariantSufficientKernelIsFutureSafe :
  ∀ {State Action Observation Latent}
    (representation :
      FutureSufficientInvariantRepresentation State Action Observation Latent)
    {left right : State} →
  encode representation left ≡ encode representation right →
  Future.FutureObservationEquivalent
    (Bridge.deterministicSystem
      (step representation) (actionLabel representation))
    (observe representation) left right
invariantSufficientKernelIsFutureSafe representation codeEqual =
  Bridge.traceEquivalentImpliesCanonicalFutureEquivalent
    (latentKernelImpliesTraceObservationEquality representation codeEqual)

invariantRepresentationIsFutureLanguageSafeProjection :
  ∀ {State Action Observation Latent}
    (representation :
      FutureSufficientInvariantRepresentation State Action Observation Latent) →
  Future.FutureLanguageSafeProjection
    (Bridge.deterministicSystem
      (step representation) (actionLabel representation))
    (observe representation)
    (encode representation)
invariantRepresentationIsFutureLanguageSafeProjection representation =
  Future.futureLanguageSafeProjection
    (invariantSufficientKernelIsFutureSafe representation)

------------------------------------------------------------------------
-- Boundary: "subspace" here means a dynamics-closed latent carrier.  A later
-- linear/spectral owner may additionally prove that Latent is a vector space,
-- that each latentStep is linear, or that the coordinates diagonalize an
-- operator.  Future safety itself needs only the two factorization laws above.
------------------------------------------------------------------------
