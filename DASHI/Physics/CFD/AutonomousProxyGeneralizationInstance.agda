module DASHI.Physics.CFD.AutonomousProxyGeneralizationInstance where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.CFD.AutonomousProxyGeneralization

toggle : Bool → Bool
toggle true = false
toggle false = true

canonicalOperator : Operator Bool
canonicalOperator = operator toggle

emptyTrace : FiniteTrace Bool
emptyTrace = finiteTrace zero impossible
  where
    impossible : Fin zero → Bool
    impossible ()

canonicalLearner : Learner Bool
canonicalLearner training = canonicalOperator

canonicalSeed : Bool
canonicalSeed = false

canonicalReference : ReferenceTimeline Bool
canonicalReference = referenceTimeline referenceAt
  where
    referenceAt : Nat → Bool
    referenceAt zero = false
    referenceAt (suc n) = toggle (referenceAt n)

canonicalDecode : DecodeChart Bool Bool
canonicalDecode = decodeChart (λ x → x)

canonicalBackend : BackendImplementation Bool
canonicalBackend = backendImplementation toggle

canonicalParity : BackendParity canonicalOperator canonicalBackend
canonicalParity = backendParity (λ x → refl)

oneStepParityProof :
  BackendImplementation.runStep canonicalBackend canonicalSeed
    ≡ autonomousTimeline canonicalOperator canonicalSeed (suc zero)
oneStepParityProof =
  parityLiftsToOneStep
    canonicalOperator
    canonicalBackend
    canonicalParity
    canonicalSeed

referenceIndependenceProof :
  autonomousFromTraining canonicalLearner emptyTrace canonicalSeed (suc zero)
    ≡ autonomousFromTraining canonicalLearner emptyTrace canonicalSeed (suc zero)
referenceIndependenceProof =
  referenceTailIrrelevant
    canonicalLearner
    emptyTrace
    canonicalSeed
    canonicalReference
    canonicalReference
    (suc zero)

extendedHorizonComparison :
  HoldoutComparison Bool Bool Bool extendedHorizon
extendedHorizonComparison = holdoutComparison
  canonicalOperator
  canonicalSeed
  (λ x → x)
  canonicalReference
  boolEqual
  extendedHorizonWitness
  where
    boolEqual : Bool → Bool → Bool
    boolEqual true true = true
    boolEqual false false = true
    boolEqual _ _ = false

firstPredictionIsTrue :
  HoldoutComparison.predicted extendedHorizonComparison (suc zero) ≡ true
firstPredictionIsTrue = refl

firstComparisonPasses :
  HoldoutComparison.measured extendedHorizonComparison (suc zero) ≡ true
firstComparisonPasses = refl
