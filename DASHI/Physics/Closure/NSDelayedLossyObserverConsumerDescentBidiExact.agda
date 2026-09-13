module DASHI.Physics.Closure.NSDelayedLossyObserverConsumerDescentBidiExact where

------------------------------------------------------------------------
-- DELAY LOSSY OBSERVERS UNTIL THE DECLARED CONSUMER DESCENDS THROUGH THEM
--
-- This is a proof-search / representation-ordering rule, not a new analytic
-- estimate.  Reuse the canonical consumer-descent machinery:
--
--   observer may move earlier
--     only when the downstream consumer factors through that observer.
--
-- A concrete collision is enough to prohibit such reordering for that exact
-- consumer.  This captures the recurring NS failure mode in which sign or
-- coherence is discarded by |.|, norm/square, positive-part, count/mean, etc.
-- before the signed cancellation / commutator / gluing consumer has run.
--
-- IMPORTANT: this does NOT claim norms, absolute values, squares, means, or
-- positive majorants are globally invalid.  They are legitimate after the
-- exact consumer has run, or earlier when an explicit FactorsThrough witness
-- proves that the consumer descends through the coarser surface.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as Aggregate

------------------------------------------------------------------------
-- 1. Minimal sign-forgetting regression.
--
-- `sameMagnitude` abstracts the only fact used by abs/norm/square-like
-- observers here: +x and -x can have the same coarse magnitude surface.
------------------------------------------------------------------------

data SignedRouteState : Set where
  positiveRoute negativeRoute : SignedRouteState

data MagnitudeSurface : Set where
  sameMagnitude : MagnitudeSurface

data SignedOutcome : Set where
  positiveOutcome negativeOutcome : SignedOutcome

signForgettingObserver : SignedRouteState → MagnitudeSurface
signForgettingObserver positiveRoute = sameMagnitude
signForgettingObserver negativeRoute = sameMagnitude

signedConsumer : SignedRouteState → SignedOutcome
signedConsumer positiveRoute = positiveOutcome
signedConsumer negativeRoute = negativeOutcome

signedOutcomesDiffer : positiveOutcome ≡ negativeOutcome → ⊥
signedOutcomesDiffer ()

signForgettingNonDescent :
  Descent.ConsumerNonDescentWitness signForgettingObserver signedConsumer
signForgettingNonDescent =
  Descent.consumerNonDescentWitness
    positiveRoute negativeRoute refl signedOutcomesDiffer

signForgettingCannotPrecedeSignedConsumer :
  Descent.FactorsThrough signForgettingObserver signedConsumer → ⊥
signForgettingCannotPrecedeSignedConsumer =
  Descent.nonDescentWitnessBlocksFactorization signForgettingNonDescent

signForgettingCannotBeSufficientForSignedConsumer :
  Descent.ConsumerSufficient signForgettingObserver signedConsumer → ⊥
signForgettingCannotBeSufficientForSignedConsumer =
  Descent.nonDescentWitnessBlocksSufficiency signForgettingNonDescent

------------------------------------------------------------------------
-- 2. Existing aggregate-direction regression.
--
-- Do not invent a second "mean" ontology.  The repo already owns a concrete
-- many-to-one aggregate: forward and reverse disagreement remain distinct on
-- the fine binary comparison but have the same accept-count.  Treat that as
-- the canonical aggregate-loss witness shape.
------------------------------------------------------------------------

aggregateDirectionObserver : Aggregate.BalancedComparison9 → Nat
aggregateDirectionObserver state =
  Aggregate.acceptCount (Aggregate.binaryProjectPositiveOnly state)

aggregateDirectionConsumer :
  Aggregate.BalancedComparison9 → Aggregate.BinaryComparison4
aggregateDirectionConsumer = Aggregate.binaryProjectPositiveOnly

aggregateDirectionNonDescent :
  Descent.ConsumerNonDescentWitness
    aggregateDirectionObserver aggregateDirectionConsumer
aggregateDirectionNonDescent =
  Descent.consumerNonDescentWitness
    Aggregate.forwardDisagreement
    Aggregate.reverseDisagreement
    Aggregate.aggregateErasesDisagreementDirection
    Aggregate.binaryDirectionStillDistinct

aggregateCannotPrecedeDirectionSensitiveConsumer :
  Descent.FactorsThrough aggregateDirectionObserver aggregateDirectionConsumer → ⊥
aggregateCannotPrecedeDirectionSensitiveConsumer =
  Descent.nonDescentWitnessBlocksFactorization aggregateDirectionNonDescent

------------------------------------------------------------------------
-- 3. Generic reusable rule.
------------------------------------------------------------------------

lossyObserverCannotMoveBeforeConsumer :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  Descent.FactorsThrough observe consumer →
  ⊥
lossyObserverCannotMoveBeforeConsumer =
  Descent.nonDescentWitnessBlocksFactorization

lossyObserverCannotBeDeclaredSufficientAfterCollision :
  ∀ {State Surface Outcome : Set}
    {observe : State → Surface}
    {consumer : State → Outcome} →
  Descent.ConsumerNonDescentWitness observe consumer →
  Descent.ConsumerSufficient observe consumer →
  ⊥
lossyObserverCannotBeDeclaredSufficientAfterCollision =
  Descent.nonDescentWitnessBlocksSufficiency

repairOfLossyObserverMustRestoreLostCoordinate :
  ∀ {State Surface Refinement Outcome : Set}
    {observe : State → Surface}
    {refine : State → Refinement}
    {consumer : State → Outcome} →
  (witness : Descent.ConsumerNonDescentWitness observe consumer) →
  Repair.RefinementRepairs observe refine consumer →
  refine (Descent.left witness) ≡ refine (Descent.right witness) →
  ⊥
repairOfLossyObserverMustRestoreLostCoordinate =
  Repair.refinementRepairSeparatesWitness

------------------------------------------------------------------------
-- 4. NS interpretation boundary.
------------------------------------------------------------------------

record DelayedLossyObserverBoundary : Set where
  constructor delayed-lossy-observer-boundary
  field
    signForgettingAutomaticallySafeBeforeSignedConsumer : Bool
    aggregateAutomaticallySafeBeforeDirectionConsumer : Bool
    explicitConsumerDescentCanLicenseEarlyLossyObserver : Bool
    normsAndAbsoluteValuesGloballyForbidden : Bool
    meanOrCountZeroMeansNoUnderlyingCancellation : Bool
    delayedObserverRuleIsConsumerIndexed : Bool
    empiricalThetaMagnitudeIsNSTheorem : Bool

canonicalDelayedLossyObserverBoundary : DelayedLossyObserverBoundary
canonicalDelayedLossyObserverBoundary =
  delayed-lossy-observer-boundary
    false false true false false true false

signForgettingAutomaticallySafeBeforeSignedConsumerIsFalse :
  DelayedLossyObserverBoundary.signForgettingAutomaticallySafeBeforeSignedConsumer
    canonicalDelayedLossyObserverBoundary ≡ false
signForgettingAutomaticallySafeBeforeSignedConsumerIsFalse = refl

aggregateAutomaticallySafeBeforeDirectionConsumerIsFalse :
  DelayedLossyObserverBoundary.aggregateAutomaticallySafeBeforeDirectionConsumer
    canonicalDelayedLossyObserverBoundary ≡ false
aggregateAutomaticallySafeBeforeDirectionConsumerIsFalse = refl

explicitConsumerDescentCanLicenseEarlyLossyObserverIsTrue :
  DelayedLossyObserverBoundary.explicitConsumerDescentCanLicenseEarlyLossyObserver
    canonicalDelayedLossyObserverBoundary ≡ true
explicitConsumerDescentCanLicenseEarlyLossyObserverIsTrue = refl

normsAndAbsoluteValuesGloballyForbiddenIsFalse :
  DelayedLossyObserverBoundary.normsAndAbsoluteValuesGloballyForbidden
    canonicalDelayedLossyObserverBoundary ≡ false
normsAndAbsoluteValuesGloballyForbiddenIsFalse = refl
