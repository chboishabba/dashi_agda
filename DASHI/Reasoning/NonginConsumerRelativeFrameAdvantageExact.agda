module DASHI.Reasoning.NonginConsumerRelativeFrameAdvantageExact where

------------------------------------------------------------------------
-- NONGIN CONSUMER-RELATIVE FRAME ADVANTAGE
--
-- The historical "1.0 -> 1.1" language is interpreted here as an exact
-- consumer-relative distinction theorem.  A coarse observation is inadequate
-- only when it identifies two fine states that a declared consumer must keep
-- distinct.  A richer representation pays the repair only when that consumer
-- factors through it exactly.
--
-- No percentage, dimensionality, intelligence, strategic superiority or
-- empirical performance law is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Philosophy.NonginOriginFormalizationExact as Origin

record ConsumerDistinguishesCollision
    {Fine Coarse Output : Set}
    (projection : Origin.LossyProjection Fine Coarse)
    (consumer : Fine → Output) : Set where
  constructor consumer-distinguishes-collision
  field
    differentConsumerOutput :
      consumer (Origin.hiddenLeft projection)
      ≡ consumer (Origin.hiddenRight projection) → ⊥

open ConsumerDistinguishesCollision public

collisionToNonDescentWitness :
  ∀ {Fine Coarse Output : Set}
    {projection : Origin.LossyProjection Fine Coarse}
    {consumer : Fine → Output} →
  ConsumerDistinguishesCollision projection consumer →
  Descent.ConsumerNonDescentWitness (Origin.project projection) consumer
collisionToNonDescentWitness {projection = projection} witness =
  Descent.consumerNonDescentWitness
    (Origin.hiddenLeft projection)
    (Origin.hiddenRight projection)
    (Origin.sameCoarse projection)
    (differentConsumerOutput witness)

CoarseConsumerFactorizationImpossible :
  ∀ {Fine Coarse Output : Set}
    (projection : Origin.LossyProjection Fine Coarse)
    (consumer : Fine → Output) → Set₁
CoarseConsumerFactorizationImpossible projection consumer =
  Descent.FactorsThrough (Origin.project projection) consumer → ⊥

consumerDistinctionBlocksCoarseFactorization :
  ∀ {Fine Coarse Output : Set}
    {projection : Origin.LossyProjection Fine Coarse}
    {consumer : Fine → Output} →
  ConsumerDistinguishesCollision projection consumer →
  CoarseConsumerFactorizationImpossible projection consumer
consumerDistinctionBlocksCoarseFactorization witness =
  Descent.nonDescentWitnessBlocksFactorization
    (collisionToNonDescentWitness witness)

ConsumerSufficientRefinement :
  ∀ {Fine Rich Output : Set} →
  (Fine → Output) → (Fine → Rich) → Set₁
ConsumerSufficientRefinement consumer refine =
  Factorized.FactorizedRefinement consumer refine

consumerRecoveryIsSufficientRefinement :
  ∀ {Fine Rich Output : Set}
    (consumer : Fine → Output)
    (refine : Fine → Rich)
    (recover : Rich → Output) →
  ((fine : Fine) → consumer fine ≡ recover (refine fine)) →
  ConsumerSufficientRefinement consumer refine
consumerRecoveryIsSufficientRefinement consumer refine recover exact =
  Factorized.factorizedRefinement recover exact

------------------------------------------------------------------------
-- Canonical historical fixture.
------------------------------------------------------------------------

hiddenOtherConsumer : Origin.DebateState → Origin.Bit
hiddenOtherConsumer = Origin.other

visibleSelfConsumer : Origin.DebateState → Origin.Bit
visibleSelfConsumer = Origin.self

historicalOtherCoordinateDistinguishesCollision :
  ConsumerDistinguishesCollision
    Origin.debateHiddenStateWitness
    hiddenOtherConsumer
historicalOtherCoordinateDistinguishesCollision =
  consumer-distinguishes-collision distinct
  where
  distinct : Origin.bit0 ≡ Origin.bit1 → ⊥
  distinct ()

historicalCoarseFrameCannotServeOtherConsumer :
  CoarseConsumerFactorizationImpossible
    Origin.debateHiddenStateWitness
    hiddenOtherConsumer
historicalCoarseFrameCannotServeOtherConsumer =
  consumerDistinctionBlocksCoarseFactorization
    historicalOtherCoordinateDistinguishesCollision

historicalPublicFrameNotSufficientForOther :
  Descent.ConsumerSufficient Origin.publicBinaryFrame hiddenOtherConsumer →
  ⊥
historicalPublicFrameNotSufficientForOther =
  Descent.nonDescentWitnessBlocksSufficiency
    (collisionToNonDescentWitness
      historicalOtherCoordinateDistinguishesCollision)

selectedCollisionDoesNotDistinguishVisibleSelf :
  visibleSelfConsumer
    (Origin.hiddenLeft Origin.debateHiddenStateWitness)
  ≡
  visibleSelfConsumer
    (Origin.hiddenRight Origin.debateHiddenStateWitness)
selectedCollisionDoesNotDistinguishVisibleSelf = refl

visibleSelfCannotSupplyDistinctionWitness :
  ConsumerDistinguishesCollision
    Origin.debateHiddenStateWitness
    visibleSelfConsumer → ⊥
visibleSelfCannotSupplyDistinctionWitness witness =
  differentConsumerOutput witness
    selectedCollisionDoesNotDistinguishVisibleSelf

richDebateObserver : Origin.DebateState → Origin.DebateState
richDebateObserver state = state

otherConsumerRecoversExactlyFromRichObserver :
  ConsumerSufficientRefinement hiddenOtherConsumer richDebateObserver
otherConsumerRecoversExactlyFromRichObserver =
  consumerRecoveryIsSufficientRefinement
    hiddenOtherConsumer
    richDebateObserver
    Origin.other
    (λ state → refl)

------------------------------------------------------------------------
-- Information-order strengthening.
--
-- The generic consumer-descent core proves that a consumer's own observation
-- is the canonical least-informative sufficient observer.  Specializing that
-- theorem here strengthens the single collision witness into a universal
-- refinement requirement for every observer that claims adequacy for the
-- hidden-other consumer.
------------------------------------------------------------------------

historicalOtherConsumerIsLeast :
  Descent.LeastSufficientConsumerObserver hiddenOtherConsumer
historicalOtherConsumerIsLeast =
  Descent.canonicalConsumerObserverIsLeast hiddenOtherConsumer

everyOtherAdequateObserverRefinesHiddenOther :
  ∀ {Surface : Set}
    (observe : Origin.DebateState → Surface) →
  Descent.ConsumerSufficient observe hiddenOtherConsumer →
  Observer.Refines hiddenOtherConsumer observe
everyOtherAdequateObserverRefinesHiddenOther observe sufficient =
  Descent.belowEverySufficient
    historicalOtherConsumerIsLeast
    observe
    sufficient

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

record NonginConsumerRelativeFrameAdvantageBoundary : Set where
  constructor nongin-consumer-relative-frame-advantage-boundary
  field
    consumerRelativeNonfactorabilityPaid : Bool
    nondistinguishingCollisionPaysAdvantage : Bool
    exactConsumerRecoveryPaid : Bool
    richerCardinalityAlonePaysAdvantage : Bool
    literalTenPercentLawPromoted : Bool
    guaranteedStrategicOutcomePromoted : Bool

open NonginConsumerRelativeFrameAdvantageBoundary public

canonicalNonginConsumerRelativeFrameAdvantageBoundary :
  NonginConsumerRelativeFrameAdvantageBoundary
canonicalNonginConsumerRelativeFrameAdvantageBoundary =
  nongin-consumer-relative-frame-advantage-boundary
    true
    false
    true
    false
    false
    false

record NonginLeastSufficientObserverBoundary : Set where
  constructor nongin-least-sufficient-observer-boundary
  field
    hiddenOtherConsumerIsLeastSufficient : Bool
    everyAdequateObserverRefinesHiddenOther : Bool
    publicBinaryFrameAdequateForHiddenOther : Bool
    leastSufficientMeansWorldComplete : Bool
    oneObserverBestForEveryConsumer : Bool

open NonginLeastSufficientObserverBoundary public

canonicalNonginLeastSufficientObserverBoundary :
  NonginLeastSufficientObserverBoundary
canonicalNonginLeastSufficientObserverBoundary =
  nongin-least-sufficient-observer-boundary
    true true false false false
