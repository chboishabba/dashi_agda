module DASHI.Core.SharedSourceUncertaintyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Coupled models often share upstream uncertain inputs.  Counting downstream
-- error terms as though they were independent can therefore duplicate one
-- source root.  This module keeps source identity explicit and proves a finite
-- duplicate-counting witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_+_)

record UncertaintySource : Set where
  constructor uncertaintySource
  field
    sourceId : String
    magnitude : Nat
    provenance : List String

open UncertaintySource public

data ConsumerKind : Set where
  erosionConsumer machineryConsumer habitatConsumer : ConsumerKind

record PropagatedUncertainty : Set where
  constructor propagatedUncertainty
  field
    consumer : ConsumerKind
    source : UncertaintySource
    sensitivityLabel : String

open PropagatedUncertainty public

sharedDEM : UncertaintySource
sharedDEM = uncertaintySource "DEM" 1 ("terrain survey" ∷ [])

erosionDEM : PropagatedUncertainty
erosionDEM = propagatedUncertainty erosionConsumer sharedDEM "slope/flow routing"

machineryDEM : PropagatedUncertainty
machineryDEM = propagatedUncertainty machineryConsumer sharedDEM "access grade"

sameRootAcrossConsumers :
  source erosionDEM ≡ source machineryDEM
sameRootAcrossConsumers = refl

naiveDownstreamBudget : PropagatedUncertainty → PropagatedUncertainty → Nat
naiveDownstreamBudget left right =
  magnitude (source left) + magnitude (source right)

uniqueRootBudgetForSharedPair : PropagatedUncertainty → PropagatedUncertainty → Nat
uniqueRootBudgetForSharedPair left right = magnitude (source left)

naivePairCountsSharedUnitTwice :
  naiveDownstreamBudget erosionDEM machineryDEM ≡ 2
naivePairCountsSharedUnitTwice = refl

uniqueSharedRootCountsOnce :
  uniqueRootBudgetForSharedPair erosionDEM machineryDEM ≡ 1
uniqueSharedRootCountsOnce = refl

record SharedSourcePair (left right : PropagatedUncertainty) : Set where
  constructor sharedSourcePair
  field
    sameSource : source left ≡ source right

open SharedSourcePair public

canonicalSharedDEMPair : SharedSourcePair erosionDEM machineryDEM
canonicalSharedDEMPair = sharedSourcePair refl

record ConsumerLocalUncertaintyFamily : Set where
  constructor consumerLocalUncertaintyFamily
  field
    propagated : List PropagatedUncertainty
    sourceAccountingPolicy : String
    correlationStructureRetained : Bool

canonicalConsumerLocalUncertaintyFamily : ConsumerLocalUncertaintyFamily
canonicalConsumerLocalUncertaintyFamily =
  consumerLocalUncertaintyFamily
    (erosionDEM ∷ machineryDEM ∷ [])
    "aggregate by provenance root before any independence assumption"
    true

record SharedSourceUncertaintyBoundary : Set where
  constructor sharedSourceUncertaintyBoundary
  field
    downstreamMultiplicityNeedNotMeanIndependentUncertainty : Bool
    commonInputCanCorrelateDifferentModelOutputs : Bool
    provenanceRootShouldSurviveConsumerProjection : Bool
    scalarCombinationNeedsDeclaredDependenceRule : Bool

canonicalSharedSourceUncertaintyBoundary : SharedSourceUncertaintyBoundary
canonicalSharedSourceUncertaintyBoundary =
  sharedSourceUncertaintyBoundary true true true true
