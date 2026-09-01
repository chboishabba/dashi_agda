module DASHI.Governance.SexedHistoricalStratifiedFutureConeQuotientExact where

open import DASHI.Core.Prelude

import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalStratifiedCounterfactualPathExact as Path

------------------------------------------------------------------------
-- SAME PRESENT / SAME IMMEDIATE CHOICE, DIFFERENT FUTURE CONE
------------------------------------------------------------------------

data FuturePathHistory : Set where
  repairedThenPluralised
  repairedThenInstitutionalised
  : FuturePathHistory

data PresentSurface : Set where
  sameEndpointStratumFidelityChoice : PresentSurface

data ImmediateChoice : Set where
  continueReciprocalSearch : ImmediateChoice

data FutureConeCode : Set where
  pluralNegotiationCone
  institutionalReciprocityCone
  : FutureConeCode

observeFuturePath : FuturePathHistory → PresentSurface
observeFuturePath _ = sameEndpointStratumFidelityChoice

immediateChoice : FuturePathHistory → ImmediateChoice
immediateChoice _ = continueReciprocalSearch

futureCone : FuturePathHistory → FutureConeCode
futureCone repairedThenPluralised = pluralNegotiationCone
futureCone repairedThenInstitutionalised = institutionalReciprocityCone

sameImmediateChoice :
  immediateChoice repairedThenPluralised
  ≡ immediateChoice repairedThenInstitutionalised
sameImmediateChoice = refl

futureConesDiffer :
  futureCone repairedThenPluralised
  ≡ futureCone repairedThenInstitutionalised → ⊥
futureConesDiffer ()

futureSurface : HistoryChoice.HistoryConditionedFutureConeSurface
futureSurface =
  record
    { FutureHistory = FuturePathHistory
    ; FutureObservation = PresentSurface
    ; FutureConeCode = FutureConeCode
    ; observeFutureHistory = observeFuturePath
    ; futureCone = futureCone
    ; futureReading =
        "Two histories may share present endpoint/stratum/fidelity and immediate action while retaining distinct continuation cones."
    }

canonicalSameObservationDifferentFutureCone :
  HistoryChoice.SameObservationDifferentFutureCone futureSurface
canonicalSameObservationDifferentFutureCone =
  record
    { futureLeftHistory = repairedThenPluralised
    ; futureRightHistory = repairedThenInstitutionalised
    ; futureSameObservation = refl
    ; futureConesDiffer = λ ()
    }

presentSurfaceCannotRecoverFutureCone :
  INF.FactorsThrough observeFuturePath futureCone → ⊥
presentSurfaceCannotRecoverFutureCone =
  HistoryChoice.futureConeCannotDescendThroughPresentObservation
    canonicalSameObservationDifferentFutureCone

------------------------------------------------------------------------
-- Continuity with admitted-path owner.
------------------------------------------------------------------------

canonicalImmediatePathChoiceRemainsHistorySensitive :
  INF.FactorsThrough Path.observePath Path.chooseNext → ⊥
canonicalImmediatePathChoiceRemainsHistorySensitive =
  Path.coarsePathCannotRecoverNextChoice

------------------------------------------------------------------------
-- Boundary: today's action closure is weaker than tomorrow's cone closure.
------------------------------------------------------------------------

data SameImmediateChoiceMeansSameFutureCone : Set where

data FutureConeDifferenceRefutesImmediateChoice : Set where

data FutureConeCodeIsPrediction : Set where

data SameStratumMeansSameFutureCone : Set where

sameImmediateChoiceDoesNotMeanSameFutureCone :
  SameImmediateChoiceMeansSameFutureCone → ⊥
sameImmediateChoiceDoesNotMeanSameFutureCone ()

futureConeDifferenceDoesNotRefuteImmediateChoice :
  FutureConeDifferenceRefutesImmediateChoice → ⊥
futureConeDifferenceDoesNotRefuteImmediateChoice ()

futureConeCodeIsNotPredictionAuthority : FutureConeCodeIsPrediction → ⊥
futureConeCodeIsNotPredictionAuthority ()

sameStratumDoesNotMeanSameFutureCone : SameStratumMeansSameFutureCone → ⊥
sameStratumDoesNotMeanSameFutureCone ()

record StratifiedFutureConeQuotientBoundary : Set where
  constructor stratified-future-cone-quotient-boundary
  field
    samePresentSurfaceExplicit : Bool
    sameImmediateChoiceExplicit : Bool
    differentFutureConesExplicit : Bool
    actionClosureImpliesFutureConeClosure : Bool
    futureConeDifferenceRefutesCurrentAction : Bool
    futureConeCodeCreatesPredictionAuthority : Bool

canonicalStratifiedFutureConeQuotientBoundary : StratifiedFutureConeQuotientBoundary
canonicalStratifiedFutureConeQuotientBoundary =
  stratified-future-cone-quotient-boundary
    true true true false false false
