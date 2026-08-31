module DASHI.Core.ConsumerRelativeSymmetryRelevanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- CONSUMER-RELATIVE SYMMETRY RELEVANCE
--
-- Cross-pollination from the 369/Monster symmetry work into the repository's
-- canonical consumer-descent calculus.
--
-- A symmetry can be mathematically genuine on a fine carrier and still be
-- irrelevant to one declared consumer.  If the consumer descends through an
-- observer and the symmetry preserves that observer, then the consumer is
-- invariant under the symmetry automatically.
--
-- Conversely, a symmetry becomes relevant to that consumer only by changing a
-- sufficient observer, or by exposing that the proposed observer was not
-- actually sufficient.
------------------------------------------------------------------------

PreservesObserver :
  ∀ {State Surface : Set} ->
  (State -> Surface) ->
  (State -> State) ->
  Set
PreservesObserver observe act =
  (x : _) -> observe (act x) ≡ observe x

ConsumerInvariantUnder :
  ∀ {State Outcome : Set} ->
  (State -> Outcome) ->
  (State -> State) ->
  Set
ConsumerInvariantUnder consumer act =
  (x : _) -> consumer (act x) ≡ consumer x

sufficientObserverPreservationImpliesConsumerInvariance :
  ∀ {State Surface Outcome : Set}
    {observe : State -> Surface}
    {consumer : State -> Outcome}
    {act : State -> State} ->
  Descent.ConsumerSufficient observe consumer ->
  PreservesObserver observe act ->
  ConsumerInvariantUnder consumer act
sufficientObserverPreservationImpliesConsumerInvariance sufficient preserves x =
  sufficient (act x) x (preserves x)

record SymmetryRelevanceWitness
    {State Surface Outcome : Set}
    (observe : State -> Surface)
    (consumer : State -> Outcome)
    (act : State -> State) : Set where
  constructor symmetryRelevanceWitness
  field
    witnessState : State
    consumerChanges : consumer (act witnessState) ≡ consumer witnessState -> ⊥

open SymmetryRelevanceWitness public

relevantSymmetryBlocksObserverPreservationWhenObserverSufficient :
  ∀ {State Surface Outcome : Set}
    {observe : State -> Surface}
    {consumer : State -> Outcome}
    {act : State -> State} ->
  Descent.ConsumerSufficient observe consumer ->
  SymmetryRelevanceWitness observe consumer act ->
  PreservesObserver observe act ->
  ⊥
relevantSymmetryBlocksObserverPreservationWhenObserverSufficient sufficient witness preserves =
  consumerChanges witness
    (sufficientObserverPreservationImpliesConsumerInvariance sufficient preserves
      (witnessState witness))

record ConsumerRelativeSymmetryBoundary : Set where
  constructor consumerRelativeSymmetryBoundary
  field
    fineSymmetryAutomaticallyRelevantToEveryConsumer : Bool
    fineSymmetryAutomaticallyRelevantToEveryConsumerIsFalse :
      fineSymmetryAutomaticallyRelevantToEveryConsumer ≡ false
    sufficientObserverPreservedBySymmetryForcesConsumerInvariance : Bool
    sufficientObserverPreservedBySymmetryForcesConsumerInvarianceIsTrue :
      sufficientObserverPreservedBySymmetryForcesConsumerInvariance ≡ true
    symmetryMayStillMatterByActingOnSufficientObserver : Bool
    symmetryMayStillMatterByActingOnSufficientObserverIsTrue :
      symmetryMayStillMatterByActingOnSufficientObserver ≡ true

canonicalConsumerRelativeSymmetryBoundary : ConsumerRelativeSymmetryBoundary
canonicalConsumerRelativeSymmetryBoundary =
  consumerRelativeSymmetryBoundary false refl true refl true refl
