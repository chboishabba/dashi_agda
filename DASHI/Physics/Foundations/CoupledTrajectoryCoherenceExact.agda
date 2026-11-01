module DASHI.Physics.Foundations.CoupledTrajectoryCoherenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A trajectory family may be enumerable and its members distinguishable
-- without being an ontology of independent alternatives.
--
-- This owner deliberately separates:
--   trajectory identity
--   common conditioning context
--   trajectory relation/coupling
--   coherent aggregation
--   observation quotient
--
-- It does not define quantum entanglement and it does not assert that every
-- physical path family is coupled in the same way.
------------------------------------------------------------------------

record CoupledTrajectoryFamily : Set₁ where
  field
    Context : Set
    Trajectory : Set
    Aggregate : Set
    Observation : Set

    contextOf : Trajectory → Context
    related : Trajectory → Trajectory → Set
    coherentAggregate : List Trajectory → Aggregate
    observeAggregate : Aggregate → Observation

    familyReading : String

open CoupledTrajectoryFamily public

record DistinctRelatedPair
    (family : CoupledTrajectoryFamily) : Set where
  field
    leftTrajectory : Trajectory family
    rightTrajectory : Trajectory family

    trajectoriesDistinct :
      leftTrajectory ≡ rightTrajectory → ⊥

    shareConditioningContext :
      contextOf family leftTrajectory
      ≡
      contextOf family rightTrajectory

    trajectoriesRelated :
      related family leftTrajectory rightTrajectory

open DistinctRelatedPair public

data ToyContext : Set where
  oneExperiment : ToyContext

data ToyTrajectory : Set where
  routeA : ToyTrajectory
  routeB : ToyTrajectory

data ToyAggregate : Set where
  coherentPairAggregate : ToyAggregate

data ToyObservation : Set where
  oneObservedPattern : ToyObservation

data ToyRelation : ToyTrajectory → ToyTrajectory → Set where
  routesCoupled : ToyRelation routeA routeB

canonicalCoupledTrajectoryFamily : CoupledTrajectoryFamily
canonicalCoupledTrajectoryFamily =
  record
    { Context = ToyContext
    ; Trajectory = ToyTrajectory
    ; Aggregate = ToyAggregate
    ; Observation = ToyObservation
    ; contextOf = λ _ → oneExperiment
    ; related = ToyRelation
    ; coherentAggregate = λ _ → coherentPairAggregate
    ; observeAggregate = λ _ → oneObservedPattern
    ; familyReading =
        "Distinct trajectory representatives may share one conditioning context and a nontrivial relation before coherent aggregation and observation."
    }

canonicalDistinctRelatedPair :
  DistinctRelatedPair canonicalCoupledTrajectoryFamily
canonicalDistinctRelatedPair =
  record
    { leftTrajectory = routeA
    ; rightTrajectory = routeB
    ; trajectoriesDistinct = λ ()
    ; shareConditioningContext = refl
    ; trajectoriesRelated = routesCoupled
    }

record CoupledTrajectoryNonPromotionBoundary : Set where
  constructor coupledTrajectoryNonPromotionBoundary
  field
    distinguishableImpliesIndependentOntology : Bool
    distinguishableImpliesIndependentOntologyIsFalse :
      distinguishableImpliesIndependentOntology ≡ false

    coherentAggregateImpliesQuantumEntanglement : Bool
    coherentAggregateImpliesQuantumEntanglementIsFalse :
      coherentAggregateImpliesQuantumEntanglement ≡ false

    finiteEnumerationExhaustsUnderlyingOntology : Bool
    finiteEnumerationExhaustsUnderlyingOntologyIsFalse :
      finiteEnumerationExhaustsUnderlyingOntology ≡ false

open CoupledTrajectoryNonPromotionBoundary public

canonicalCoupledTrajectoryNonPromotionBoundary :
  CoupledTrajectoryNonPromotionBoundary
canonicalCoupledTrajectoryNonPromotionBoundary =
  coupledTrajectoryNonPromotionBoundary
    false refl
    false refl
    false refl
