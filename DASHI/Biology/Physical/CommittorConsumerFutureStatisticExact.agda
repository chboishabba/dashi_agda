module DASHI.Biology.Physical.CommittorConsumerFutureStatisticExact where

------------------------------------------------------------------------
-- A committor is sufficient for one declared future hitting question, not a
-- complete state descriptor.  Two fine chemical states below carry distinct
-- hidden catalytic provenance but induce exactly the same proto-life-before-
-- extinction distribution for every supplied query trace.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Cognition.PNF.RationalProbabilityFutureKernelExact as Prob

------------------------------------------------------------------------
-- Fine state and coarse target-event law.
------------------------------------------------------------------------

data CatalyticHistory : Set where mineralRoute organicRoute : CatalyticHistory

record FineChemicalState : Set where
  constructor fineChemicalState
  field
    history : CatalyticHistory
    targetBeforeExtinction : Prob.BinaryProbability

open FineChemicalState public

halfHalf : Prob.BinaryProbability
halfHalf =
  Prob.binaryProbability ½ ½
    Prob.halfNonnegative Prob.halfNonnegative solve-∀

mineralState organicState : FineChemicalState
mineralState = fineChemicalState mineralRoute halfHalf
organicState = fineChemicalState organicRoute halfHalf

committorObservation : FineChemicalState → ℚ
committorObservation x = Prob.trueMass (targetBeforeExtinction x)

sameCommittor : committorObservation mineralState ≡ committorObservation organicState
sameCommittor = refl

historiesRemainDistinct : history mineralState ≢ history organicState
historiesRemainDistinct ()

------------------------------------------------------------------------
-- Every trace has the same binary hitting-event distribution.  Actions are
-- deliberately abstract query labels because this theorem is about consumer
-- sufficiency, not a second chemical dynamics model.
------------------------------------------------------------------------

data QueryAction : Set where askAgain : QueryAction

targetEventKernel : Prob.RationalProbabilityFutureKernel FineChemicalState QueryAction
targetEventKernel = Prob.rationalProbabilityFutureKernel λ state actions →
  targetBeforeExtinction state

sameTargetFutureLaw :
  Prob.ProbabilityFutureEquivalent targetEventKernel mineralState organicState
sameTargetFutureLaw = Prob.probabilityFutureEquivalent λ actions → refl

------------------------------------------------------------------------
-- A broader consumer observing catalytic history separates them immediately.
------------------------------------------------------------------------

historyObservation : FineChemicalState → CatalyticHistory
historyObservation = history

sameTargetLawDoesNotDetermineHistory :
  Prob.ProbabilityFutureEquivalent targetEventKernel mineralState organicState
  × historyObservation mineralState ≢ historyObservation organicState
sameTargetLawDoesNotDetermineHistory = sameTargetFutureLaw , historiesRemainDistinct

record CommittorSufficiencyBoundary : Set where
  field
    committorSufficientForDeclaredBinaryHittingConsumer : Bool
    committorSufficientForDeclaredBinaryHittingConsumerIsTrue :
      committorSufficientForDeclaredBinaryHittingConsumer ≡ true
    committorSufficientForAllChemicalConsumers : Bool
    committorSufficientForAllChemicalConsumersIsFalse :
      committorSufficientForAllChemicalConsumers ≡ false

canonicalCommittorSufficiencyBoundary : CommittorSufficiencyBoundary
canonicalCommittorSufficiencyBoundary = record
  { committorSufficientForDeclaredBinaryHittingConsumer = true
  ; committorSufficientForDeclaredBinaryHittingConsumerIsTrue = refl
  ; committorSufficientForAllChemicalConsumers = false
  ; committorSufficientForAllChemicalConsumersIsFalse = refl
  }
