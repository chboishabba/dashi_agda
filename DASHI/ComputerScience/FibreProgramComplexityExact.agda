module DASHI.ComputerScience.FibreProgramComplexityExact where

open import DASHI.Core.Prelude
open import Data.List using (length)

------------------------------------------------------------------------
-- FIBRE-INDEXED PROGRAM COMPLEXITY
--
-- Program complexity is not collapsed to a single scalar.  A computation can
-- have distinct description, execution, storage, representation, trace, and
-- residual/provenance costs.  Which coordinates matter is consumer-indexed.
------------------------------------------------------------------------

record ComplexityProfile : Set where
  constructor complexityProfile
  field
    sourceDescriptionCost : Nat
    programStorageCost : Nat
    dataStorageCost : Nat
    executionStepCost : Nat
    registerStateCost : Nat
    representationCellCost : Nat
    traceCost : Nat
    residualWitnessCost : Nat

open ComplexityProfile public

record ComplexityConsumer : Set₁ where
  constructor complexityConsumer
  field
    Outcome : Set
    observeComplexity : ComplexityProfile → Outcome

open ComplexityConsumer public

sourceDescriptionConsumer : ComplexityConsumer
sourceDescriptionConsumer =
  complexityConsumer Nat sourceDescriptionCost

executionStepConsumer : ComplexityConsumer
executionStepConsumer =
  complexityConsumer Nat executionStepCost

representationCellConsumer : ComplexityConsumer
representationCellConsumer =
  complexityConsumer Nat representationCellCost

------------------------------------------------------------------------
-- PATH-INDEXED COMPLEXITY
--
-- A complexity profile is a summary receipt.  The deeper object is an actual
-- path through an execution/storage/register fibre.  Cost is then selected by
-- a consumer K_C rather than being built into the path itself.
------------------------------------------------------------------------

record ExecutionFibrePath (State : Set) : Set where
  constructor executionFibrePath
  field
    states : List State

open ExecutionFibrePath public

pathStateCount :
  ∀ {State : Set} →
  ExecutionFibrePath State →
  Nat
pathStateCount path = length (states path)

transitionCountList :
  ∀ {State : Set} →
  List State →
  Nat
transitionCountList [] = 0
transitionCountList (_ ∷ []) = 0
transitionCountList (_ ∷ y ∷ ys) =
  suc (transitionCountList (y ∷ ys))

pathTransitionCount :
  ∀ {State : Set} →
  ExecutionFibrePath State →
  Nat
pathTransitionCount path = transitionCountList (states path)

record PathCostConsumer (State : Set) : Set₁ where
  constructor pathCostConsumer
  field
    Outcome : Set
    costPath : ExecutionFibrePath State → Outcome

open PathCostConsumer public

K :
  ∀ {State : Set} →
  (consumer : PathCostConsumer State) →
  ExecutionFibrePath State →
  PathCostConsumer.Outcome consumer
K consumer path = costPath consumer path

stateVisitConsumer :
  ∀ {State : Set} →
  PathCostConsumer State
stateVisitConsumer = pathCostConsumer Nat pathStateCount

transitionConsumer :
  ∀ {State : Set} →
  PathCostConsumer State
transitionConsumer = pathCostConsumer Nat pathTransitionCount

------------------------------------------------------------------------
-- Generic scalar observations along a path.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

maxNat : Nat → Nat → Nat
maxNat 0 n = n
maxNat (suc m) 0 = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

maximumNat : List Nat → Nat
maximumNat [] = 0
maximumNat (x ∷ xs) = maxNat x (maximumNat xs)

mapMeasure :
  ∀ {State : Set} →
  (State → Nat) →
  List State →
  List Nat
mapMeasure measure [] = []
mapMeasure measure (state ∷ rest) =
  measure state ∷ mapMeasure measure rest

sumMeasure :
  ∀ {State : Set} →
  (State → Nat) →
  ExecutionFibrePath State →
  Nat
sumMeasure measure path =
  sumNat (mapMeasure measure (states path))

peakMeasure :
  ∀ {State : Set} →
  (State → Nat) →
  ExecutionFibrePath State →
  Nat
peakMeasure measure path =
  maximumNat (mapMeasure measure (states path))

sumMeasureConsumer :
  ∀ {State : Set} →
  (State → Nat) →
  PathCostConsumer State
sumMeasureConsumer measure =
  pathCostConsumer Nat (sumMeasure measure)

peakMeasureConsumer :
  ∀ {State : Set} →
  (State → Nat) →
  PathCostConsumer State
peakMeasureConsumer measure =
  pathCostConsumer Nat (peakMeasure measure)

------------------------------------------------------------------------
-- Head-path complexity.
--
-- The head itself is an address-valued observation of execution state.
-- Distance is deliberately representation-neutral here; later memory/layout
-- fibres may replace Nat distance with cache-line, network, physical, or loom
-- geometry without changing the abstract execution path.
------------------------------------------------------------------------

natDistance : Nat → Nat → Nat
natDistance 0 n = n
natDistance n 0 = n
natDistance (suc m) (suc n) = natDistance m n

headTravelList :
  ∀ {State : Set} →
  (State → Nat) →
  List State →
  Nat
headTravelList head [] = 0
headTravelList head (_ ∷ []) = 0
headTravelList head (x ∷ y ∷ rest) =
  natDistance (head x) (head y)
  + headTravelList head (y ∷ rest)

headTravelCost :
  ∀ {State : Set} →
  (State → Nat) →
  ExecutionFibrePath State →
  Nat
headTravelCost head path =
  headTravelList head (states path)

headTravelConsumer :
  ∀ {State : Set} →
  (State → Nat) →
  PathCostConsumer State
headTravelConsumer head =
  pathCostConsumer Nat (headTravelCost head)

record FibreComplexityBoundary : Set where
  constructor fibreComplexityBoundary
  field
    oneScalarIsCanonicalForEveryConsumer : Bool
    executionCostEqualsDescriptionCost : Bool
    representationCostEqualsSemanticCost : Bool
    residualProvenanceCanBeTrackedSeparately : Bool
    complexityIsConsumerIndexed : Bool
    complexityCanBePathIndexed : Bool
    headPathIsAComplexityCoordinate : Bool
    physicalDistanceAlreadyAssumed : Bool

canonicalFibreComplexityBoundary : FibreComplexityBoundary
canonicalFibreComplexityBoundary =
  fibreComplexityBoundary false false false true true true true false
