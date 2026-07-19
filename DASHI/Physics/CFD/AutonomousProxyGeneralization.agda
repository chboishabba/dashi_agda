module DASHI.Physics.CFD.AutonomousProxyGeneralization where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- CORE / CFD separation.
--
-- CORE evolves a compact proxy state autonomously.  CFD/LES appears only as
-- a source of finite training traces and as an optional observer/reference
-- lane.  In particular, the autonomous rollout function below has no LES
-- timeline argument, so future reference states cannot be consulted by
-- construction.
------------------------------------------------------------------------

record Operator (State : Set) : Set where
  constructor operator
  field
    step : State → State

record FiniteTrace (State : Set) : Set where
  constructor finiteTrace
  field
    length : Nat
    at : Fin length → State

Learner : Set → Set
Learner State = FiniteTrace State → Operator State

iterate : {State : Set} → (State → State) → Nat → State → State
iterate f zero x = x
iterate f (suc n) x = iterate f n (f x)

autonomousTimeline :
  {State : Set} →
  Operator State →
  State →
  Nat →
  State
autonomousTimeline op seed t = iterate (Operator.step op) t seed

autonomousFromTraining :
  {State : Set} →
  Learner State →
  FiniteTrace State →
  State →
  Nat →
  State
autonomousFromTraining learn training seed =
  autonomousTimeline (learn training) seed

------------------------------------------------------------------------
-- Reference tails are observational inputs only.
------------------------------------------------------------------------

record ReferenceTimeline (State : Set) : Set where
  constructor referenceTimeline
  field
    at : Nat → State

referenceTailIrrelevant :
  {State : Set} →
  (learn : Learner State) →
  (training : FiniteTrace State) →
  (seed : State) →
  (reference₁ reference₂ : ReferenceTimeline State) →
  (t : Nat) →
  autonomousFromTraining learn training seed t
    ≡ autonomousFromTraining learn training seed t
referenceTailIrrelevant learn training seed reference₁ reference₂ t = refl

------------------------------------------------------------------------
-- Decode is a chart/observer, not part of CORE evolution.
------------------------------------------------------------------------

record DecodeChart (State Field : Set) : Set where
  constructor decodeChart
  field
    decode : State → Field

decodedTimeline :
  {State Field : Set} →
  DecodeChart State Field →
  Operator State →
  State →
  Nat →
  Field
decodedTimeline chart op seed t =
  DecodeChart.decode chart (autonomousTimeline op seed t)

decodeChoiceDoesNotChangeCore :
  {State Field₁ Field₂ : Set} →
  (chart₁ : DecodeChart State Field₁) →
  (chart₂ : DecodeChart State Field₂) →
  (op : Operator State) →
  (seed : State) →
  (t : Nat) →
  autonomousTimeline op seed t ≡ autonomousTimeline op seed t
decodeChoiceDoesNotChangeCore chart₁ chart₂ op seed t = refl

------------------------------------------------------------------------
-- Evaluation relations and the generalization boundary.
--
-- A score on the same trajectory and same initial condition is an in-sample
-- reconstruction result.  Generalization requires a typed witness that the
-- evaluation relation crosses at least one genuine boundary.
------------------------------------------------------------------------

data EvaluationRelation : Set where
  inSampleReplay : EvaluationRelation
  heldOutTime : EvaluationRelation
  unseenInitialCondition : EvaluationRelation
  shiftedParameters : EvaluationRelation
  extendedHorizon : EvaluationRelation

data GeneralizationWitness : EvaluationRelation → Set where
  heldOutTimeWitness : GeneralizationWitness heldOutTime
  unseenInitialConditionWitness : GeneralizationWitness unseenInitialCondition
  shiftedParametersWitness : GeneralizationWitness shiftedParameters
  extendedHorizonWitness : GeneralizationWitness extendedHorizon

data ⊥ : Set where

inSampleReplayIsNotGeneralization :
  GeneralizationWitness inSampleReplay → ⊥
inSampleReplayIsNotGeneralization ()

record EvaluationResult
  (State Observation Score : Set)
  (relation : EvaluationRelation) : Set₁ where
  constructor evaluationResult
  field
    operator : Operator State
    seed : State
    observe : State → Observation
    reference : ReferenceTimeline Observation
    score : Score
    generalization : GeneralizationWitness relation

------------------------------------------------------------------------
-- A holdout evaluator may compare an autonomous proxy timeline with a CFD/LES
-- reference, but the reference is not an input to the rollout itself.
------------------------------------------------------------------------

record HoldoutComparison
  (State Observation Score : Set)
  (relation : EvaluationRelation) : Set₁ where
  constructor holdoutComparison
  field
    learnedOperator : Operator State
    seed : State
    decode : State → Observation
    reference : ReferenceTimeline Observation
    compare : Observation → Observation → Score
    witness : GeneralizationWitness relation

  predicted : Nat → Observation
  predicted t = decode (autonomousTimeline learnedOperator seed t)

  measured : Nat → Score
  measured t = compare predictedAt referenceAt
    where
      predictedAt : Observation
      predictedAt = predicted t

      referenceAt : Observation
      referenceAt = ReferenceTimeline.at reference t

------------------------------------------------------------------------
-- Backend semantics.
--
-- CPU, Vulkan, or another implementation may execute the same operator.  A
-- backend claim is valid only when a parity witness relates the implementations.
------------------------------------------------------------------------

record BackendImplementation (State : Set) : Set where
  constructor backendImplementation
  field
    runStep : State → State

record BackendParity {State : Set}
  (specification : Operator State)
  (implementation : BackendImplementation State) : Set where
  constructor backendParity
  field
    stepParity :
      (x : State) →
      BackendImplementation.runStep implementation x
        ≡ Operator.step specification x

parityLiftsToOneStep :
  {State : Set} →
  (specification : Operator State) →
  (implementation : BackendImplementation State) →
  BackendParity specification implementation →
  (x : State) →
  BackendImplementation.runStep implementation x
    ≡ autonomousTimeline specification x (suc zero)
parityLiftsToOneStep specification implementation parity x =
  BackendParity.stepParity parity x
