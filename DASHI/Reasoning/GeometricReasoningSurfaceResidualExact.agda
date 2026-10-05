module DASHI.Reasoning.GeometricReasoningSurfaceResidualExact where

------------------------------------------------------------------------
-- GEOMETRIC SURFACE + DEPENDENT RESIDUAL ROUTING
--
-- DASHI CONTRIBUTION
--
-- Cross-pollinates the mature surface/residual codec discipline into geometric
-- reasoning.  The geometric surface may be enough for one consumer while a
-- magnitude-, history-, orientation-, or composition-sensitive consumer needs
-- a dependent residual.  No surface is promoted to a complete representation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record GeometricSurfaceCode (State Surface : Set) : Set₁ where
  constructor geometric-surface-code
  field
    surface : State → Surface
    Residual : Surface → Set
    residual : (state : State) → Residual (surface state)
    reopen : (s : Surface) → Residual s → State
    reopenExact :
      (state : State) →
      reopen (surface state) (residual state) ≡ state
    provenance : String

open GeometricSurfaceCode public

data GeometricConsumerClass : Set where
  surfaceOnly : GeometricConsumerClass
  selectedResidual : GeometricConsumerClass
  fullState : GeometricConsumerClass

record SurfaceConsumerFactors
    {State Surface Output : Set}
    (code : GeometricSurfaceCode State Surface)
    (consumer : State → Output) : Set₁ where
  constructor surface-consumer-factors
  field
    consumeSurface : Surface → Output
    factors :
      (state : State) →
      consumer state ≡ consumeSurface (surface code state)

open SurfaceConsumerFactors public

record SelectedResidualConsumer
    {State Surface Output : Set}
    (code : GeometricSurfaceCode State Surface)
    (consumer : State → Output) : Set₁ where
  constructor selected-residual-consumer
  field
    Selected : (s : Surface) → Residual code s → Set
    consumeSelected :
      (s : Surface) →
      (r : Residual code s) →
      Selected s r → Output
    selectedSufficient :
      (state : State) →
      (receipt : Selected (surface code state) (residual code state)) →
      consumer state
      ≡ consumeSelected
          (surface code state)
          (residual code state)
          receipt

-- A collision is a concrete non-descent witness.  The repository deliberately
-- does not turn this record alone into a universal theorem about an arbitrary
-- caller-supplied factorisation; each consumer proves its own contradiction.
record SurfaceCollision
    {State Surface Output : Set}
    (surface : State → Surface)
    (consumer : State → Output) : Set where
  constructor surface-collision
  field
    left right : State
    sameSurface : surface left ≡ surface right
    differentConsumer : consumer left ≡ consumer right → ⊥

open SurfaceCollision public

record GeometricReasoningSurfaceResidualBoundary : Set where
  constructor geometric-reasoning-surface-residual-boundary
  field
    dependentResidualTyped : Bool
    exactReopenRequired : Bool
    surfaceOnlyConsumerTyped : Bool
    selectedResidualConsumerTyped : Bool
    collisionWitnessTyped : Bool
    genericCollisionAutoPromotedToUniversalNonDescent : Bool
    geometricSurfaceAutomaticallyComplete : Bool
    residualAvailabilityAutomaticallyProvesNecessity : Bool

canonicalGeometricReasoningSurfaceResidualBoundary :
  GeometricReasoningSurfaceResidualBoundary
canonicalGeometricReasoningSurfaceResidualBoundary =
  geometric-reasoning-surface-residual-boundary
    true true true true true false false false
