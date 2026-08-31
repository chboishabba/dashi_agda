module DASHI.Core.ConsumerRelativeCoarseGrainingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ObserverRefinementExact as Refinement
import DASHI.Core.ConsumerRelativeMinimalFidelityExact as Minimal
import DASHI.Core.ConsumerReductionDependencyReopeningExact as Reopening
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Bidi

------------------------------------------------------------------------
-- CONSUMER-RELATIVE COARSE-GRAINING / RENORMALISATION BIDI SPINE
--
-- A coarse observer can be exact for one declared consumer while remaining
-- insufficient for another.  The retained relative-fine residual is therefore
-- not 'noise' by definition: whether it matters is consumer-relative.
--
-- This is the shared information geometry behind fMRI/connectome projections,
-- learned NN representations, effective physical descriptions, chemistry
-- summaries and cosmological/macroscopic parameter descriptions.
------------------------------------------------------------------------

data DomainReading : Set where
  neuralPopulationReading
  learnedRepresentationReading
  quantumEffectiveReading
  chemicalCollectiveReading
  cosmologicalEffectiveReading
  : DomainReading

record CoarseGrainingApplicationReceipt : Set where
  constructor coarse-graining-application-receipt
  field
    domain : DomainReading
    fineCarrierReference : String
    coarseObserverReference : String
    relativeFineResidualReference : String
    declaredConsumerReference : String
    dynamicsClosureReference : String
    factorisationReference : String
    collisionSearchReference : String
    refinementReference : String
    dependencyReopeningReference : String
    validationReference : String

fibreBoundary : Fibre.CoarseFineRelativeFibreBoundary
fibreBoundary = Fibre.canonicalCoarseFineRelativeFibreBoundary

minimalBoundary : Minimal.MinimalFidelityBoundary
minimalBoundary = Minimal.canonicalMinimalFidelityBoundary

reopeningBoundary : Reopening.ReductionDependencyReopeningBoundary
reopeningBoundary = Reopening.canonicalReductionDependencyReopeningBoundary

activeBidiBoundary : Bidi.ActiveBidiDiscriminatorLoopBoundary
activeBidiBoundary = Bidi.canonicalActiveBidiDiscriminatorLoopBoundary

record ConsumerRelativeCoarseGrainingBoundary : Set where
  constructor consumer-relative-coarse-graining-boundary
  field
    coarseDescriptionCanBeExactForDeclaredConsumer : Bool
    coarseDescriptionCanBeExactForDeclaredConsumerIsTrue :
      coarseDescriptionCanBeExactForDeclaredConsumer ≡ true
    exactForOneConsumerImpliesExactForEveryConsumer : Bool
    exactForOneConsumerImpliesExactForEveryConsumerIsFalse :
      exactForOneConsumerImpliesExactForEveryConsumer ≡ false
    relativeFineResidualIsAutomaticallyNoise : Bool
    relativeFineResidualIsAutomaticallyNoiseIsFalse :
      relativeFineResidualIsAutomaticallyNoise ≡ false
    highestFidelityIsAlwaysRequired : Bool
    highestFidelityIsAlwaysRequiredIsFalse :
      highestFidelityIsAlwaysRequired ≡ false
    coarseCollisionCanRequireObserverRefinement : Bool
    coarseCollisionCanRequireObserverRefinementIsTrue :
      coarseCollisionCanRequireObserverRefinement ≡ true
    refinementAutomaticallyChangesWorldState : Bool
    refinementAutomaticallyChangesWorldStateIsFalse :
      refinementAutomaticallyChangesWorldState ≡ false
    changedFineCoordinateMayReopenDependentConsumersTransitively : Bool
    changedFineCoordinateMayReopenDependentConsumersTransitivelyIsTrue :
      changedFineCoordinateMayReopenDependentConsumersTransitively ≡ true
    unrelatedConsumersMustReopenWithoutDependencyPath : Bool
    unrelatedConsumersMustReopenWithoutDependencyPathIsFalse :
      unrelatedConsumersMustReopenWithoutDependencyPath ≡ false
    reading : String

canonicalConsumerRelativeCoarseGrainingBoundary :
  ConsumerRelativeCoarseGrainingBoundary
canonicalConsumerRelativeCoarseGrainingBoundary =
  consumer-relative-coarse-graining-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    "Coarse-graining is judged relative to a declared downstream consumer. A coarse observer may exactly preserve one consumer while collapsing distinctions required by another. Relative-fine information is retained as a reopenable residual, observer refinement supplies a BIDI repair path, and only dependency-affected downstream certificates need reopen when a fine coordinate changes."
