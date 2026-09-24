module DASHI.Law.SensibLawPabaiComparativeWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Law.SensibLawPabaiDefeaterRefinementRerunExact as Pabai
import DASHI.Law.SensibLawComparativeWorldIRExact as Comparative

------------------------------------------------------------------------
-- M11 / S26.4 PABAI COMPARATIVE REGRESSION
--
-- W0 = reachable support route.
-- W1 = same route after exact core-policy defeater is admitted.
-- W2 = reviewed transformation/counterfactual candidate that reopens search.
--
-- W2 remains candidate-only; this module does not promote it to current law.
------------------------------------------------------------------------

data PabaiWorld : Set where
  w0SupportReachable : PabaiWorld
  w1DefeaterAdmitted : PabaiWorld
  w2CounterCandidate : PabaiWorld

data RouteStatus : Set where
  reachableCandidate : RouteStatus
  defeated : RouteStatus

routeStatus : PabaiWorld → RouteStatus
routeStatus w0SupportReachable = reachableCandidate
routeStatus w1DefeaterAdmitted = defeated
routeStatus w2CounterCandidate = reachableCandidate

data PabaiInputDelta : Set where
  corePolicyDefeaterD : PabaiInputDelta
  counterDistinctionC : PabaiInputDelta

applyFromW0 : PabaiInputDelta → RouteStatus
applyFromW0 corePolicyDefeaterD = defeated
applyFromW0 counterDistinctionC = reachableCandidate

applyFromW1 : PabaiInputDelta → RouteStatus
applyFromW1 corePolicyDefeaterD = defeated
applyFromW1 counterDistinctionC = reachableCandidate

w0ToW1ExactDistinction :
  applyFromW0 corePolicyDefeaterD ≡ routeStatus w1DefeaterAdmitted
w0ToW1ExactDistinction = refl

w1ToW2ExactDistinction :
  applyFromW1 counterDistinctionC ≡ routeStatus w2CounterCandidate
w1ToW2ExactDistinction = refl

------------------------------------------------------------------------
-- Existing executable/proof-relevant owners pay the route states.
------------------------------------------------------------------------

w0ExecutableReachable :
  Search.reachable 1 Regression.pabaiGraph Pabai.pabaiFactsBeforeDefeater
    Negligence.dutyProposition ≡ true
w0ExecutableReachable = Pabai.pabaiReachableBeforeDefeater

w1ExecutableDefeated :
  Search.reachable 1 Regression.pabaiGraph Pabai.pabaiFactsAfterDefeater
    Negligence.dutyProposition ≡ false
w1ExecutableDefeated = Pabai.pabaiUnreachableAfterDefeater

w2ExistingTransformationReopens :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
w2ExistingTransformationReopens = Pabai.pabaiExistingRepairCandidateStillReopens

------------------------------------------------------------------------
-- Static world-difference noise is not the answer-changing distinction.
------------------------------------------------------------------------

data IrrelevantPabaiNoise : Set where
  presentationOrderChanged : IrrelevantPabaiNoise
  unrelatedSourceLabelChanged : IrrelevantPabaiNoise

noiseDoesNotChangeW0Route :
  (noise : IrrelevantPabaiNoise) →
  routeStatus w0SupportReachable ≡ reachableCandidate
noiseDoesNotChangeW0Route noise = refl

data RouteStatusChangeCausesItself : Set where
data CounterCandidateIsCurrentLaw : Set where
data UnrelatedNoiseIsExactDistinction : Set where

routeStatusOutcomeDoesNotCauseItself :
  RouteStatusChangeCausesItself → ⊥
routeStatusOutcomeDoesNotCauseItself ()

counterCandidateStillNotCurrentLaw :
  CounterCandidateIsCurrentLaw → ⊥
counterCandidateStillNotCurrentLaw ()

irrelevantNoiseIsNotExactDistinction :
  UnrelatedNoiseIsExactDistinction → ⊥
irrelevantNoiseIsNotExactDistinction ()

record PabaiComparativeBoundary : Set where
  constructor pabaiComparativeBoundary
  field
    w0Reachable : Bool
    w0ReachableIsTrue : w0Reachable ≡ true

    w1Defeated : Bool
    w1DefeatedIsTrue : w1Defeated ≡ true

    w2ReopenedCandidate : Bool
    w2ReopenedCandidateIsTrue : w2ReopenedCandidate ≡ true

    w0ToW1AnswerChangingAtomIsDefeater : Bool
    w0ToW1AnswerChangingAtomIsDefeaterIsTrue :
      w0ToW1AnswerChangingAtomIsDefeater ≡ true

    w1ToW2AnswerChangingAtomIsCounterDistinction : Bool
    w1ToW2AnswerChangingAtomIsCounterDistinctionIsTrue :
      w1ToW2AnswerChangingAtomIsCounterDistinction ≡ true

    outcomeDeltaServesAsOwnCause : Bool
    outcomeDeltaServesAsOwnCauseIsFalse :
      outcomeDeltaServesAsOwnCause ≡ false

    candidateRepairPromotedToCurrentLaw : Bool
    candidateRepairPromotedToCurrentLawIsFalse :
      candidateRepairPromotedToCurrentLaw ≡ false

open PabaiComparativeBoundary public

canonicalPabaiComparativeBoundary : PabaiComparativeBoundary
canonicalPabaiComparativeBoundary =
  pabaiComparativeBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
