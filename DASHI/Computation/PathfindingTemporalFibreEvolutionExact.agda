module DASHI.Computation.PathfindingTemporalFibreEvolutionExact where

-- Time-indexed pathfinding fibres.
-- A search is not a single quotient snapshot: each step carries a fine state,
-- a consumer-visible observation, and a residual carrier that may itself change
-- under transport.  Any preservation/splitting/reopening claim must therefore
-- be indexed by the same literal transition.

open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)

------------------------------------------------------------------------
-- 1. Stable temporal fibre system.
------------------------------------------------------------------------

record TemporalPathfindingFibre : Set₁ where
  constructor temporalPathfindingFibre
  field
    Time : Set
    State : Time → Set
    Observation : Time → Set
    Residual : Time → Set

    observe : (t : Time) → State t → Observation t
    residual : (t : Time) → State t → Residual t

    nextTime : Time → Time
    step : (t : Time) → State t → State (nextTime t)

    transportObservation :
      (t : Time) → Observation t → Observation (nextTime t)

    transportResidual :
      (t : Time) → Residual t → Residual (nextTime t)

    observationCommutes :
      (t : Time) (x : State t) →
      observe (nextTime t) (step t x) ≡
      transportObservation t (observe t x)

open TemporalPathfindingFibre public

------------------------------------------------------------------------
-- 2. Same-object transition receipt.
------------------------------------------------------------------------

record TemporalTransitionReceipt
  (F : TemporalPathfindingFibre)
  (t : Time F)
  (x : State F t) : Set where
  constructor temporalTransitionReceipt
  field
    sourceObservation : Observation F t
    sourceResidual : Residual F t
    targetObservation : Observation F (nextTime F t)
    targetResidual : Residual F (nextTime F t)

    sourceObservationExact :
      sourceObservation ≡ observe F t x
    sourceResidualExact :
      sourceResidual ≡ residual F t x
    targetObservationExact :
      targetObservation ≡ observe F (nextTime F t) (step F t x)
    targetResidualExact :
      targetResidual ≡ residual F (nextTime F t) (step F t x)

open TemporalTransitionReceipt public

------------------------------------------------------------------------
-- 3. Residual evolution kinds.
--
-- These are named transition roles, not cardinality claims.  An implementation
-- may inhabit one only when it supplies the corresponding relation on the same
-- literal source and target residual carriers.
------------------------------------------------------------------------

data ResidualEvolutionKind : Set where
  preservedResidual : ResidualEvolutionKind
  refinedResidual : ResidualEvolutionKind
  mergedResidual : ResidualEvolutionKind
  reopenedResidual : ResidualEvolutionKind
  invalidatedResidual : ResidualEvolutionKind

record ResidualEvolutionWitness
  (F : TemporalPathfindingFibre)
  (t : Time F)
  (x : State F t) : Set₁ where
  constructor residualEvolutionWitness
  field
    kind : ResidualEvolutionKind
    relates :
      Residual F t → Residual F (nextTime F t) → Set
    sourceTargetRelated :
      relates
        (residual F t x)
        (residual F (nextTime F t) (step F t x))

open ResidualEvolutionWitness public

------------------------------------------------------------------------
-- 4. Consumer equality at one time does not imply temporal identity.
------------------------------------------------------------------------

record SameObservationAt
  (F : TemporalPathfindingFibre)
  (t : Time F)
  (x y : State F t) : Set where
  constructor sameObservationAt
  field
    observationEqual : observe F t x ≡ observe F t y

open SameObservationAt public

record TemporalFibreBoundary : Set where
  constructor temporalFibreBoundary
  field
    sameObservationNowImpliesSameFutureResidual : Bool
    sameObservationNowImpliesSameFutureResidualIsFalse :
      sameObservationNowImpliesSameFutureResidual ≡ false

    residualCarrierMayChangeAcrossTime : Bool
    residualCarrierMayChangeAcrossTimeIsTrue :
      residualCarrierMayChangeAcrossTime ≡ true

    transitionMayReopenPreviouslyHiddenInformation : Bool
    transitionMayReopenPreviouslyHiddenInformationIsTrue :
      transitionMayReopenPreviouslyHiddenInformation ≡ true

    temporalTransportMayBeInferredFromCardinality : Bool
    temporalTransportMayBeInferredFromCardinalityIsFalse :
      temporalTransportMayBeInferredFromCardinality ≡ false

canonicalTemporalFibreBoundary : TemporalFibreBoundary
canonicalTemporalFibreBoundary =
  temporalFibreBoundary false refl true refl true refl false refl
