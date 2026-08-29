module DASHI.Analysis.RiemannG21ContextualAlternativeFiniteInstanceExact where

open import DASHI.Core.Prelude

import DASHI.Analysis.RiemannG21ContextualAlternativeNonpromotionExact as Context

------------------------------------------------------------------------
-- Concrete inhabitant of the generic contextual-alternative interface using
-- the finite three-source witness extracted from Jiang et al. 2026.
------------------------------------------------------------------------

data AggregateObservation : Set where
  sameDetectedCoherentSetup : AggregateObservation

sameDescription : Context.GroupingContext → Context.GroupingContext → Set
sameDescription _ _ = ⊤

incompatibleNarrative :
  Context.GroupingContext → Context.GroupingContext → Set
incompatibleNarrative c₁ c₂ =
  Context.naiveNarrative c₁ ≡ Context.naiveNarrative c₂ → ⊥

canonicalContextualAlternativeDescription :
  Context.ContextualAlternativeDescription
canonicalContextualAlternativeDescription = record
  { PhysicalSystem = Context.ThreeSourceSetup
  ; Context = Context.GroupingContext
  ; Alternative = Context.GroupedAlternative
  ; Amplitude = Context.AmplitudeStatus
  ; Observation = AggregateObservation
  ; system = Context.sameThreeCrystalExperiment
  ; alternatives = Context.contextAlternative
  ; amplitude = Context.contextAmplitude
  ; aggregateObservation = λ _ → sameDetectedCoherentSetup
  ; SamePhysicalDescription = sameDescription
  ; IncompatibleOriginNarrative = incompatibleNarrative
  ; sameObjectiveSystemAcrossContexts = λ _ _ _ → ⊤
  ; incompatibleNarrativesCanShareObjectiveDescription = λ _ _ _ _ → ⊤
  }

firstAndSecondContextsShareAggregateObservation :
  Context.aggregateObservation canonicalContextualAlternativeDescription
    Context.groupingABGivenC
  ≡
  Context.aggregateObservation canonicalContextualAlternativeDescription
    Context.groupingAGivenBC
firstAndSecondContextsShareAggregateObservation = refl

firstAndSecondNarrativesAreIncompatible :
  Context.IncompatibleOriginNarrative canonicalContextualAlternativeDescription
    Context.groupingABGivenC Context.groupingAGivenBC
firstAndSecondNarrativesAreIncompatible = Context.naiveNarrativesDiffer

firstGroupedAlternativeIsAdmissible :
  Context.alternatives canonicalContextualAlternativeDescription
    Context.groupingABGivenC Context.groupedAB
firstGroupedAlternativeIsAdmissible = tt

secondGroupedAlternativeIsAdmissible :
  Context.alternatives canonicalContextualAlternativeDescription
    Context.groupingAGivenBC Context.groupedBC
secondGroupedAlternativeIsAdmissible = tt

record ContextualAlternativeFiniteInstanceBoundary : Set where
  constructor contextualAlternativeFiniteInstanceBoundary
  field
    genericInterfaceInhabited : Bool
    genericInterfaceInhabitedIsTrue : genericInterfaceInhabited ≡ true
    sameAggregateObservationAcrossGroupings : Bool
    sameAggregateObservationAcrossGroupingsIsTrue :
      sameAggregateObservationAcrossGroupings ≡ true
    incompatibleNarrativesWitnessed : Bool
    incompatibleNarrativesWitnessedIsTrue : incompatibleNarrativesWitnessed ≡ true
    physicalOriginUniquenessDerived : Bool
    physicalOriginUniquenessDerivedIsFalse : physicalOriginUniquenessDerived ≡ false

canonicalContextualAlternativeFiniteInstanceBoundary :
  ContextualAlternativeFiniteInstanceBoundary
canonicalContextualAlternativeFiniteInstanceBoundary =
  contextualAlternativeFiniteInstanceBoundary
    true refl true refl true refl false refl
