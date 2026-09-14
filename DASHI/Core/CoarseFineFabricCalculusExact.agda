module DASHI.Core.CoarseFineFabricCalculusExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- PROJECTION COLLISION / CONSUMER NON-FACTORABILITY
--
-- This is deliberately weaker than CoarseFineRelativeFibreExact: a projection
-- collision does not require a relative-fine coordinate, section, reopening,
-- dynamics, or quotient structure.  It records only the information needed to
-- refute a coarse-only consumer factorisation.
------------------------------------------------------------------------

record ProjectionCollision
    {Fine Coarse Observation : Set}
    (project : Fine → Coarse)
    (observe : Fine → Observation) : Set where
  constructor projectionCollision
  field
    left right : Fine
    sameProjection : project left ≡ project right
    consumerSeparates : observe left ≡ observe right → ⊥

open ProjectionCollision public

consumerCannotFactorThroughProjection :
  ∀ {Fine Coarse Observation : Set}
    {project : Fine → Coarse}
    {observe : Fine → Observation} →
  ProjectionCollision project observe →
  (coarseObserve : Coarse → Observation) →
  ((state : Fine) → observe state ≡ coarseObserve (project state)) →
  ⊥
consumerCannotFactorThroughProjection collision coarseObserve factors =
  consumerSeparates collision
    (trans
      (factors (left collision))
      (trans
        (cong coarseObserve (sameProjection collision))
        (sym (factors (right collision)))))

------------------------------------------------------------------------
-- Boundary: this tranche proves only a static consumer/non-factorability law.
------------------------------------------------------------------------

staticNonrecoverabilityIsDynamicNoncongruence : Bool
staticNonrecoverabilityIsDynamicNoncongruence = false

hyperfabric369PromotedAsGenericFabricInThisTranche : Bool
hyperfabric369PromotedAsGenericFabricInThisTranche = false

record CoarseFineFabricCalculusBoundary : Set where
  constructor coarseFineFabricCalculusBoundary
  field
    projectionCollisionNeedsExactReopening : Bool
    staticLossAlreadyProvesDynamicNoncongruence : Bool
    refinementIsInverseProjectionAutomatically : Bool
    hyperfabric369IsTheGenericFabric : Bool

canonicalCoarseFineFabricCalculusBoundary : CoarseFineFabricCalculusBoundary
canonicalCoarseFineFabricCalculusBoundary =
  coarseFineFabricCalculusBoundary false false false false
