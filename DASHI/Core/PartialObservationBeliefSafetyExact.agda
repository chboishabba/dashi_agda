module DASHI.Core.PartialObservationBeliefSafetyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- A present observation is generally not a Markov state.  This module lifts
-- DASHI's future-safety discipline to history/belief representations and gives
-- an exact finite counterexample in which two histories have the same current
-- observation but a common probe exposes different futures.
--
-- REFERENCE / MOTIVATION
--
-- Zhaohan Guo, Huazheng Wang, Xin Liu, Yang Yu,
-- "Provably Efficient Representation Learning with Tractable Planning in
-- Low-Rank POMDP", ICML 2023, Proceedings of Machine Learning Research 202.
-- No DOI is asserted here.
--
-- The paper motivates history/belief representations for partially observable
-- control.  The exact finite theorems below are DASHI constructions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.GenericFuturePartitionRefinementExact as Future

------------------------------------------------------------------------
-- A belief machine is an exact predictive-state quotient of interaction
-- histories when both observation and action update factor through the belief.
------------------------------------------------------------------------

record BeliefStateMachine
    (History Action Belief Observation : Set) : Set₁ where
  constructor beliefStateMachine
  field
    currentObservation : History → Observation
    advanceHistory : Action → History → History
    encodeBelief : History → Belief
    observeBelief : Belief → Observation
    updateBelief : Action → Belief → Belief

    currentFactorsThroughBelief :
      ∀ history →
      currentObservation history
      ≡ observeBelief (encodeBelief history)

    updateCommutes :
      ∀ action history →
      encodeBelief (advanceHistory action history)
      ≡ updateBelief action (encodeBelief history)

open BeliefStateMachine public

runBelief :
  ∀ {History Action Belief Observation} →
  BeliefStateMachine History Action Belief Observation →
  List Action → Belief → Belief
runBelief machine = Future.run (updateBelief machine)

runHistory :
  ∀ {History Action Belief Observation} →
  BeliefStateMachine History Action Belief Observation →
  List Action → History → History
runHistory machine = Future.run (advanceHistory machine)

beliefRunCommutes :
  ∀ {History Action Belief Observation}
    (machine : BeliefStateMachine History Action Belief Observation)
    (actions : List Action)
    (history : History) →
  encodeBelief machine (runHistory machine actions history)
  ≡ runBelief machine actions (encodeBelief machine history)
beliefRunCommutes machine [] history = refl
beliefRunCommutes machine (action ∷ rest) history
  rewrite updateCommutes machine action history =
  beliefRunCommutes machine rest (advanceHistory machine action history)

sameBeliefPreservesFiniteFutureObservation :
  ∀ {History Action Belief Observation}
    (machine : BeliefStateMachine History Action Belief Observation)
    (actions : List Action)
    {left right : History} →
  encodeBelief machine left ≡ encodeBelief machine right →
  currentObservation machine (runHistory machine actions left)
  ≡ currentObservation machine (runHistory machine actions right)
sameBeliefPreservesFiniteFutureObservation machine actions same
  rewrite currentFactorsThroughBelief machine (runHistory machine actions _)
        | currentFactorsThroughBelief machine (runHistory machine actions _)
        | beliefRunCommutes machine actions _
        | beliefRunCommutes machine actions _
        | same = refl

------------------------------------------------------------------------
-- Current-observation insufficiency witness.
------------------------------------------------------------------------

data DemoHistory : Set where
  leftPast rightPast leftAfter rightAfter : DemoHistory

data DemoAction : Set where
  probe : DemoAction

data DemoObservation : Set where
  sameNow leftResponse rightResponse : DemoObservation

currentDemo : DemoHistory → DemoObservation
currentDemo leftPast = sameNow
currentDemo rightPast = sameNow
currentDemo leftAfter = leftResponse
currentDemo rightAfter = rightResponse

advanceDemo : DemoAction → DemoHistory → DemoHistory
advanceDemo probe leftPast = leftAfter
advanceDemo probe rightPast = rightAfter
advanceDemo probe leftAfter = leftAfter
advanceDemo probe rightAfter = rightAfter

currentObservationCollision : currentDemo leftPast ≡ currentDemo rightPast
currentObservationCollision = refl

futureResponseDistinguishes :
  currentDemo (advanceDemo probe leftPast)
  ≡ currentDemo (advanceDemo probe rightPast) → ⊥
futureResponseDistinguishes ()

record CurrentObservationTerminalisationDefect : Set where
  constructor currentObservationTerminalisationDefect
  field
    sameCurrent : currentDemo leftPast ≡ currentDemo rightPast
    sameProbeFutureImpossible :
      currentDemo (advanceDemo probe leftPast)
      ≡ currentDemo (advanceDemo probe rightPast) → ⊥

canonicalCurrentObservationTerminalisationDefect :
  CurrentObservationTerminalisationDefect
canonicalCurrentObservationTerminalisationDefect =
  currentObservationTerminalisationDefect
    currentObservationCollision
    futureResponseDistinguishes

------------------------------------------------------------------------
-- Boundary: wrapping a current sensor value in a type called "state" does not
-- repair partial observability.  A belief/predictive state earns promotion only
-- when its update and relevant future observations actually factor through it.
------------------------------------------------------------------------

record PartialObservationBoundary : Set where
  constructor partialObservationBoundary
  field
    currentObservationNeedNotBeMarkovState : Agda.Builtin.Bool.Bool
    equalCurrentObservationNeedNotMeanEqualFuture : Agda.Builtin.Bool.Bool
    beliefSafetyNeedsUpdateCommutation : Agda.Builtin.Bool.Bool
    beliefSafetyIsConsumerAndActionLanguageRelative : Agda.Builtin.Bool.Bool

canonicalPartialObservationBoundary : PartialObservationBoundary
canonicalPartialObservationBoundary =
  partialObservationBoundary
    Agda.Builtin.Bool.true Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true Agda.Builtin.Bool.true
