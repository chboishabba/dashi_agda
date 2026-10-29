{-# OPTIONS --safe #-}
module DASHI.Interop.HierarchicalSpectralParetoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Core.RecursiveParetoFrontierLiftingExact as Recursive

------------------------------------------------------------------------
-- THRESHOLD-ORDERED QUOTIENT COARSENING
--
-- The threshold carrier is abstract. Runtime consumers may instantiate it
-- with continuous spectral distance. The theorem needs only an explicit order
-- and explicit relation inclusion. It does not introduce hidden quotient types.
------------------------------------------------------------------------

record ThresholdOrder : Set₁ where
  constructor threshold-order
  field
    Threshold : Set
    _≤τ_ : Threshold → Threshold → Set

open ThresholdOrder public

record ThresholdQuotient
    (order : ThresholdOrder)
    (Carrier : Set) : Set₁ where
  constructor threshold-quotient
  field
    threshold : Threshold order
    related : Carrier → Carrier → Set

open ThresholdQuotient public

record ThresholdCoarsening
    {order : ThresholdOrder}
    {Carrier : Set}
    (fine coarse : ThresholdQuotient order Carrier) : Set₁ where
  constructor threshold-coarsening
  field
    thresholdMonotone :
      _≤τ_ order (threshold fine) (threshold coarse)
    relationIncluded :
      ∀ {left right} →
      related fine left right →
      related coarse left right

open ThresholdCoarsening public

record QuotientClass
    {order : ThresholdOrder}
    {Carrier : Set}
    (quotient : ThresholdQuotient order Carrier) : Set₁ where
  constructor quotient-class
  field
    representative : Carrier
    member : Carrier → Set
    memberSound :
      ∀ candidate →
      member candidate →
      related quotient representative candidate
    memberComplete :
      ∀ candidate →
      related quotient representative candidate →
      member candidate

open QuotientClass public

coarsenQuotientClass :
  ∀ {order : ThresholdOrder}
    {Carrier : Set}
    {fine coarse : ThresholdQuotient order Carrier} →
  ThresholdCoarsening fine coarse →
  QuotientClass fine →
  QuotientClass coarse
coarsenQuotientClass {coarse = coarse} coarsening fineClass =
  quotient-class
    (representative fineClass)
    (λ candidate →
      related coarse (representative fineClass) candidate)
    (λ candidate evidence → evidence)
    (λ candidate evidence → evidence)

fineRelationMapsIntoCoarseRelation :
  ∀ {order : ThresholdOrder}
    {Carrier : Set}
    {fine coarse : ThresholdQuotient order Carrier} →
  (coarsening : ThresholdCoarsening fine coarse) →
  ∀ {left right} →
  related fine left right →
  related coarse left right
fineRelationMapsIntoCoarseRelation coarsening =
  relationIncluded coarsening

------------------------------------------------------------------------
-- DISCRETE WORKER CAPACITY OVER CONTINUOUS TOPIC/ALPHA COORDINATES
------------------------------------------------------------------------

record AlphaOrder : Set₁ where
  constructor alpha-order
  field
    Alpha : Set
    Weight : Set
    _≤α_ : Alpha → Alpha → Set
    weightedSum3 :
      Weight → Alpha →
      Weight → Alpha →
      Weight → Alpha →
      Alpha

open AlphaOrder public

record TopicParetoCoordinates
    (alphaOrder : AlphaOrder)
    (Topic : Set) : Set₁ where
  constructor topic-pareto-coordinates
  field
    spectralWeight : Weight alphaOrder
    theoremWeight : Weight alphaOrder
    formalGapWeight : Weight alphaOrder
    spectralEnergy : Topic → Alpha alphaOrder
    theoremDensity : Topic → Alpha alphaOrder
    formalGapReduction : Topic → Alpha alphaOrder
    alphaPriority : Topic → Alpha alphaOrder
    alphaIsWeightedCombination :
      ∀ topic →
      alphaPriority topic
      ≡
      weightedSum3 alphaOrder
        spectralWeight (spectralEnergy topic)
        theoremWeight (theoremDensity topic)
        formalGapWeight (formalGapReduction topic)
    paretoEligible : Topic → Set

open TopicParetoCoordinates public

record CapacityAwareWorkerAllocation
    {alphaOrder : AlphaOrder}
    {Topic : Set}
    (coordinates : TopicParetoCoordinates alphaOrder Topic) : Set₁ where
  constructor capacity-aware-worker-allocation
  field
    workerCapacity : Nat
    scheduledCount : Nat
    capacityBound : scheduledCount ≤ workerCapacity
    Scheduled : Topic → Set
    scheduledIsParetoEligible :
      ∀ topic →
      Scheduled topic →
      paretoEligible coordinates topic
    HigherAlphaPreferred : Topic → Topic → Set
    higherAlphaPreferenceSound :
      ∀ {preferred deferred} →
      HigherAlphaPreferred preferred deferred →
      _≤α_ alphaOrder
        (alphaPriority coordinates deferred)
        (alphaPriority coordinates preferred)
    parallelNoTypedMeetRequired : Bool
    parallelNoTypedMeetRequiredIsTrue :
      parallelNoTypedMeetRequired ≡ true
    alphaPriorityCreatesProofAuthority : Bool
    alphaPriorityCreatesProofAuthorityIsFalse :
      alphaPriorityCreatesProofAuthority ≡ false

open CapacityAwareWorkerAllocation public

allocationCannotExceedWorkerCapacity :
  ∀ {alphaOrder : AlphaOrder}
    {Topic : Set}
    {coordinates : TopicParetoCoordinates alphaOrder Topic} →
  (allocation : CapacityAwareWorkerAllocation coordinates) →
  scheduledCount allocation ≤ workerCapacity allocation
allocationCannotExceedWorkerCapacity =
  capacityBound

alphaPreferenceRespectsDeclaredOrder :
  ∀ {alphaOrder : AlphaOrder}
    {Topic : Set}
    {coordinates : TopicParetoCoordinates alphaOrder Topic} →
  (allocation : CapacityAwareWorkerAllocation coordinates) →
  ∀ {preferred deferred} →
  HigherAlphaPreferred allocation preferred deferred →
  _≤α_ alphaOrder
    (alphaPriority coordinates deferred)
    (alphaPriority coordinates preferred)
alphaPreferenceRespectsDeclaredOrder allocation =
  higherAlphaPreferenceSound allocation

------------------------------------------------------------------------
-- EXISTING PARETO AUTHORITY BOUNDARY
------------------------------------------------------------------------

existingRecursiveParetoBoundary :
  Recursive.RecursiveParetoFrontierBoundary
existingRecursiveParetoBoundary =
  Recursive.canonicalRecursiveParetoFrontierBoundary

hierarchicalSchedulerCreatesProofAuthority : Bool
hierarchicalSchedulerCreatesProofAuthority =
  Recursive.paretoFrontierRefinementCreatesProofAuthority
    existingRecursiveParetoBoundary

hierarchicalSchedulerCreatesProofAuthorityIsFalse :
  hierarchicalSchedulerCreatesProofAuthority ≡ false
hierarchicalSchedulerCreatesProofAuthorityIsFalse =
  Recursive.paretoFrontierRefinementCreatesProofAuthorityIsFalse
    existingRecursiveParetoBoundary

record HierarchicalSpectralParetoBoundary : Set where
  constructor hierarchical-spectral-pareto-boundary
  field
    thresholdCoarseningRequiresRelationInclusion : Bool
    thresholdCoarseningRequiresRelationInclusionIsTrue :
      thresholdCoarseningRequiresRelationInclusion ≡ true
    workerAllocationIsDiscrete : Bool
    workerAllocationIsDiscreteIsTrue :
      workerAllocationIsDiscrete ≡ true
    continuousAlphaCreatesProofAuthority : Bool
    continuousAlphaCreatesProofAuthorityIsFalse :
      continuousAlphaCreatesProofAuthority ≡ false
    parallelDispatchRequiresNoTypedMeet : Bool
    parallelDispatchRequiresNoTypedMeetIsTrue :
      parallelDispatchRequiresNoTypedMeet ≡ true

canonicalHierarchicalSpectralParetoBoundary :
  HierarchicalSpectralParetoBoundary
canonicalHierarchicalSpectralParetoBoundary =
  hierarchical-spectral-pareto-boundary
    true refl
    true refl
    false refl
    true refl
