module DASHI.Moonshine.DuncanSwisherConsumerResidualRefinementExact where

------------------------------------------------------------------------
-- DUNCAN--SWISHER INSTANCE OF CONSUMER-INDEXED RESIDUAL REFINEMENT
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- This file turns the support/depth controls into the same theorem shape used
-- by the Wikidata diagnostic lane:
--
--   coarse collision relevant to declared consumer
--     -> coarse observer is insufficient
--     -> every sufficient repair MUST split that collision.
--
-- The finite controls reveal TWO successive insufficiencies:
--
--   support(5)=support(7)=true, but exponent 9 /= 6;
--
--   (support,depth)(7)=(true,2)=(support,depth)(11),
--   but exponent 6 /= 2.
--
-- Thus adding the Deligne depth unit alone still does not close the consumer.
-- The source-natural sufficient statistic is (Frobenius regime, depth unit):
-- singleton/multiple/quadratic gates multiply depth by 3/1/0.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.MonsterExponentObserverRefinementExact as Refinement
import DASHI.Moonshine.MonsterOrderExponentCorrectionExact as Monster
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

------------------------------------------------------------------------
-- Declared consumer: exact Monster exponent on the six structural probes.
------------------------------------------------------------------------

exponentConsumer : Refinement.ExponentProbe → Nat
exponentConsumer Refinement.probe5 = Monster.monsterOrderExponent Lane.p5
exponentConsumer Refinement.probe7 = Monster.monsterOrderExponent Lane.p7
exponentConsumer Refinement.probe11 = Monster.monsterOrderExponent Lane.p11
exponentConsumer Refinement.probe13 = Monster.monsterOrderExponent Lane.p13
exponentConsumer Refinement.probe37 = 0
exponentConsumer Refinement.probe43 = 0

------------------------------------------------------------------------
-- First collision: Boolean support is insufficient for multiplicity.
------------------------------------------------------------------------

supportCollision57 :
  Consumer.ConsumerRelevantCollision
    Refinement.supportObservation exponentConsumer
supportCollision57 = Consumer.consumer-relevant-collision
  Refinement.probe5
  Refinement.probe7
  refl
  (λ ())

supportCannotServeExponentConsumer :
  Consumer.ConsumerSufficient Refinement.supportObservation exponentConsumer → ⊥
supportCannotServeExponentConsumer =
  Consumer.coarseCollisionBlocksSufficiency supportCollision57

anyExponentSufficientObserverMustSplitP5P7 :
  ∀ {Surface : Set}
    (observe : Refinement.ExponentProbe → Surface) →
  Consumer.ConsumerSufficient observe exponentConsumer →
  observe Refinement.probe5 ≡ observe Refinement.probe7 → ⊥
anyExponentSufficientObserverMustSplitP5P7 observe sufficient =
  Consumer.everySufficientObserverSeparatesRelevantCollision
    supportCollision57 sufficient

------------------------------------------------------------------------
-- Depth unit.  These are the source-derived Deligne/automorphism minima.
------------------------------------------------------------------------

depthUnit : Refinement.ExponentProbe → Nat
depthUnit Refinement.probe5 = 3
depthUnit Refinement.probe7 = 2
depthUnit Refinement.probe11 = 2
depthUnit Refinement.probe13 = 1
depthUnit Refinement.probe37 = 1
depthUnit Refinement.probe43 = 1

supportAndDepth : Refinement.ExponentProbe → Bool × Nat
supportAndDepth = Observer.pairObserver Refinement.supportObservation depthUnit

-- Second collision: one plausible extra coordinate is still insufficient.
supportDepthCollision711 :
  Consumer.ConsumerRelevantCollision supportAndDepth exponentConsumer
supportDepthCollision711 = Consumer.consumer-relevant-collision
  Refinement.probe7
  Refinement.probe11
  refl
  (λ ())

supportPlusDepthStillInsufficient :
  Consumer.ConsumerSufficient supportAndDepth exponentConsumer → ⊥
supportPlusDepthStillInsufficient =
  Consumer.coarseCollisionBlocksSufficiency supportDepthCollision711

anyExponentSufficientObserverMustSplitP7P11 :
  ∀ {Surface : Set}
    (observe : Refinement.ExponentProbe → Surface) →
  Consumer.ConsumerSufficient observe exponentConsumer →
  observe Refinement.probe7 ≡ observe Refinement.probe11 → ⊥
anyExponentSufficientObserverMustSplitP7P11 observe sufficient =
  Consumer.everySufficientObserverSeparatesRelevantCollision
    supportDepthCollision711 sufficient

------------------------------------------------------------------------
-- The actual gate coordinate from Theorem 1.2.
------------------------------------------------------------------------

data FrobeniusRegime : Set where
  singletonRational multipleRational nonRational : FrobeniusRegime

regime : Refinement.ExponentProbe → FrobeniusRegime
regime Refinement.probe5 = singletonRational
regime Refinement.probe7 = singletonRational
regime Refinement.probe11 = multipleRational
regime Refinement.probe13 = singletonRational
regime Refinement.probe37 = nonRational
regime Refinement.probe43 = nonRational

depthAndRegime : Refinement.ExponentProbe → Nat × FrobeniusRegime
depthAndRegime = Observer.pairObserver depthUnit regime

decodeDepthRegime : Nat × FrobeniusRegime → Nat
decodeDepthRegime (depth , singletonRational) = 3 * depth
decodeDepthRegime (depth , multipleRational) = depth
decodeDepthRegime (depth , nonRational) = 0

exponentFactorsThroughDepthRegime :
  (p : Refinement.ExponentProbe) →
  decodeDepthRegime (depthAndRegime p) ≡ exponentConsumer p
exponentFactorsThroughDepthRegime Refinement.probe5 = refl
exponentFactorsThroughDepthRegime Refinement.probe7 = refl
exponentFactorsThroughDepthRegime Refinement.probe11 = refl
exponentFactorsThroughDepthRegime Refinement.probe13 = refl
exponentFactorsThroughDepthRegime Refinement.probe37 = refl
exponentFactorsThroughDepthRegime Refinement.probe43 = refl

depthRegimeSufficientForExponent :
  Consumer.ConsumerSufficient depthAndRegime exponentConsumer
depthRegimeSufficientForExponent left right sameObserver =
  trans
    (sym (exponentFactorsThroughDepthRegime left))
    (trans
      (cong decodeDepthRegime sameObserver)
      (exponentFactorsThroughDepthRegime right))

------------------------------------------------------------------------
-- Regime is exactly the residual needed to repair the support+depth collision.
------------------------------------------------------------------------

supportDepthPlusRegimeRepair :
  Consumer.ResidualRepair supportAndDepth regime exponentConsumer
supportDepthPlusRegimeRepair = Consumer.residual-repair
  (λ left right jointSame →
    depthRegimeSufficientForExponent left right
      (cong (λ x → proj₂ (proj₁ x) , proj₂ x) jointSame))

regimeMustSplitP7P11 :
  regime Refinement.probe7 ≡ regime Refinement.probe11 → ⊥
regimeMustSplitP7P11 =
  Consumer.residualMustSeparateRelevantCollision
    supportDepthCollision711 supportDepthPlusRegimeRepair

supportDepthRegimeStrictlyRefinesSupportDepth :
  Observer.StrictRefinement
    supportAndDepth
    (Observer.pairObserver supportAndDepth regime)
supportDepthRegimeStrictlyRefinesSupportDepth =
  Consumer.consumerRelevantResidualGivesStrictRefinement
    supportDepthCollision711 supportDepthPlusRegimeRepair

------------------------------------------------------------------------
-- Boundary: sufficient statistic, not semantic identity/world completeness.
------------------------------------------------------------------------

record DuncanSwisherConsumerResidualRefinementBoundary : Set where
  field
    supportCollisionRelevantToExponent : Bool
    supportInsufficientForExponent : Bool
    supportPlusDepthStillInsufficient : Bool
    regimeResidualNecessaryOnP7P11 : Bool
    depthRegimeSufficientForSixControls : Bool
    arbitrarySufficientObserverMustSplitKnownCollisions : Bool
    depthRegimeReconstructsWholeSupersingularGeometry : Bool
    arithmeticObserverIdentifiedWithOntologyProvenance : Bool

canonicalDuncanSwisherConsumerResidualRefinementBoundary :
  DuncanSwisherConsumerResidualRefinementBoundary
canonicalDuncanSwisherConsumerResidualRefinementBoundary = record
  { supportCollisionRelevantToExponent = true
  ; supportInsufficientForExponent = true
  ; supportPlusDepthStillInsufficient = true
  ; regimeResidualNecessaryOnP7P11 = true
  ; depthRegimeSufficientForSixControls = true
  ; arbitrarySufficientObserverMustSplitKnownCollisions = true
  ; depthRegimeReconstructsWholeSupersingularGeometry = false
  ; arithmeticObserverIdentifiedWithOntologyProvenance = false
  }
