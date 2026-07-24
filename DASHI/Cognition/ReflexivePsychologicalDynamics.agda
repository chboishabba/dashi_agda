module DASHI.Cognition.ReflexivePsychologicalDynamics where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Generic coupled belief/expectation/action/world dynamics.
------------------------------------------------------------------------

record ReflexiveState
    (World Belief Expectation : Set) : Set where
  constructor reflexiveState
  field
    worldState : World
    beliefState : Belief
    expectationState : Expectation

open ReflexiveState public

record ReflexiveDynamics
    (World Belief Expectation Action Observation : Set) : Set₁ where
  field
    chooseAction :
      World → Belief → Expectation → Action

    evolveWorld :
      World → Belief → Expectation → Action → World

    observeWorld : World → Observation

    updateBelief :
      Belief → Observation → Expectation → Action → Belief

    updateExpectation :
      Expectation → Belief → Observation → Expectation

open ReflexiveDynamics public

step :
  ∀ {World Belief Expectation Action Observation} →
  ReflexiveDynamics World Belief Expectation Action Observation →
  ReflexiveState World Belief Expectation →
  ReflexiveState World Belief Expectation
step dynamics state =
  let
    action = chooseAction dynamics
      (worldState state)
      (beliefState state)
      (expectationState state)

    nextWorld = evolveWorld dynamics
      (worldState state)
      (beliefState state)
      (expectationState state)
      action

    observation = observeWorld dynamics nextWorld

    nextBelief = updateBelief dynamics
      (beliefState state)
      observation
      (expectationState state)
      action

    nextExpectation = updateExpectation dynamics
      (expectationState state)
      nextBelief
      observation
  in
  reflexiveState nextWorld nextBelief nextExpectation

------------------------------------------------------------------------
-- Observation provenance prevents action-mediated evidence from being silently
-- treated as exogenous confirmation.
------------------------------------------------------------------------

data ObservationOrigin : Set where
  exogenousOrigin : ObservationOrigin
  ownActionMediatedOrigin : ObservationOrigin
  collectiveActionMediatedOrigin : ObservationOrigin
  policyMediatedOrigin : ObservationOrigin
  unknownOrigin : ObservationOrigin

record SituatedObservation
    (Observation Action : Set) : Set where
  constructor situatedObservation
  field
    payload : Observation
    origin : ObservationOrigin
    priorAction : Action

open SituatedObservation public

data ExpectationRole : Set where
  expectedWorld : ExpectationRole
  expectedPolicy : ExpectationRole
  expectedOtherAction : ExpectationRole
  expectedOthersExpectation : ExpectationRole

data PerformativeBeliefClass : Set where
  predictiveBelief : PerformativeBeliefClass
  performativeBelief : PerformativeBeliefClass
  counterperformativeBelief : PerformativeBeliefClass

record PerformativeLoopWitness
    (Belief Action World : Set) : Set₁ where
  field
    belief : Belief
    action : Action
    outcome : World
    classification : PerformativeBeliefClass
    beliefContributesToAction : Set
    actionContributesToOutcome : Set

open PerformativeLoopWitness public

------------------------------------------------------------------------
-- Finite bank-run regression: expectation changes present action, action changes
-- liquidity, and the observation updates belief.  This is a structural model,
-- not an empirical banking theorem.
------------------------------------------------------------------------

data BankWorld : Set where
  liquidBank : BankWorld
  strainedBank : BankWorld
  failedBank : BankWorld

data BankBelief : Set where
  trustBelief : BankBelief
  uncertainBelief : BankBelief
  panicBelief : BankBelief

data BankExpectation : Set where
  othersHold : BankExpectation
  othersWithdraw : BankExpectation

data BankAction : Set where
  holdFunds : BankAction
  partialWithdrawal : BankAction
  fullWithdrawal : BankAction

data BankObservation : Set where
  liquidityObserved : BankObservation
  strainObserved : BankObservation
  failureObserved : BankObservation

bankChooseAction :
  BankWorld → BankBelief → BankExpectation → BankAction
bankChooseAction _ panicBelief _ = fullWithdrawal
bankChooseAction _ uncertainBelief othersWithdraw = partialWithdrawal
bankChooseAction _ uncertainBelief othersHold = holdFunds
bankChooseAction _ trustBelief othersWithdraw = partialWithdrawal
bankChooseAction _ trustBelief othersHold = holdFunds

bankEvolveWorld :
  BankWorld → BankBelief → BankExpectation → BankAction → BankWorld
bankEvolveWorld failedBank _ _ _ = failedBank
bankEvolveWorld strainedBank _ _ fullWithdrawal = failedBank
bankEvolveWorld strainedBank _ _ partialWithdrawal = strainedBank
bankEvolveWorld strainedBank _ _ holdFunds = strainedBank
bankEvolveWorld liquidBank _ _ fullWithdrawal = strainedBank
bankEvolveWorld liquidBank _ _ partialWithdrawal = strainedBank
bankEvolveWorld liquidBank _ _ holdFunds = liquidBank

bankObserve : BankWorld → BankObservation
bankObserve liquidBank = liquidityObserved
bankObserve strainedBank = strainObserved
bankObserve failedBank = failureObserved

bankUpdateBelief :
  BankBelief → BankObservation → BankExpectation → BankAction → BankBelief
bankUpdateBelief _ failureObserved _ _ = panicBelief
bankUpdateBelief _ strainObserved _ _ = panicBelief
bankUpdateBelief trustBelief liquidityObserved _ _ = trustBelief
bankUpdateBelief uncertainBelief liquidityObserved _ _ = uncertainBelief
bankUpdateBelief panicBelief liquidityObserved _ _ = uncertainBelief

bankUpdateExpectation :
  BankExpectation → BankBelief → BankObservation → BankExpectation
bankUpdateExpectation _ panicBelief _ = othersWithdraw
bankUpdateExpectation _ uncertainBelief strainObserved = othersWithdraw
bankUpdateExpectation previous _ _ = previous

bankDynamics :
  ReflexiveDynamics
    BankWorld BankBelief BankExpectation BankAction BankObservation
bankDynamics =
  record
    { chooseAction = bankChooseAction
    ; evolveWorld = bankEvolveWorld
    ; observeWorld = bankObserve
    ; updateBelief = bankUpdateBelief
    ; updateExpectation = bankUpdateExpectation
    }

panicInitialState :
  ReflexiveState BankWorld BankBelief BankExpectation
panicInitialState =
  reflexiveState liquidBank panicBelief othersWithdraw

panicFirstStepWorldIsStrained :
  worldState (step bankDynamics panicInitialState) ≡ strainedBank
panicFirstStepWorldIsStrained = refl

panicFirstStepBeliefRemainsPanic :
  beliefState (step bankDynamics panicInitialState) ≡ panicBelief
panicFirstStepBeliefRemainsPanic = refl

panicSecondStepWorldIsFailed :
  worldState (step bankDynamics (step bankDynamics panicInitialState))
    ≡ failedBank
panicSecondStepWorldIsFailed = refl

record ReflexivePsychologyBoundary : Set where
  constructor reflexivePsychologyBoundary
  field
    coupledDynamicsFormalised : Bool
    performativityFormalised : Bool
    clinicalModelEstablished : Bool
    neurologicalMechanismEstablished : Bool
    clinicalModelEstablishedIsFalse : clinicalModelEstablished ≡ false
    neurologicalMechanismEstablishedIsFalse :
      neurologicalMechanismEstablished ≡ false

canonicalReflexivePsychologyBoundary : ReflexivePsychologyBoundary
canonicalReflexivePsychologyBoundary =
  reflexivePsychologyBoundary true true false false refl refl
