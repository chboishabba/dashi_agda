module DASHI.Core.HistoryConditionedChoiceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- HISTORY-CONDITIONED CHOICE
--
-- A history may be observationally coarse-grained without thereby becoming
-- irrelevant to present choice.  This owner separates:
--
--   fine history
--   coarse present observation
--   history-sensitive pattern / continuation summary
--   present choice
--
-- and reuses the existing generic non-factorability theorem to prove that a
-- choice consumer cannot descend through a coarse observation whenever two
-- histories share that observation but motivate different choices.
------------------------------------------------------------------------

record HistoryConditionedChoiceSurface : Set₁ where
  field
    History : Set
    Observation : Set
    Pattern : Set
    Choice : Set

    observe : History → Observation
    patternOf : History → Pattern
    choose : History → Choice

    historyReading : String

open HistoryConditionedChoiceSurface public

record DistinctHistoriesSameObservationDifferentChoice
    (surface : HistoryConditionedChoiceSurface) : Set where
  field
    leftHistory : History surface
    rightHistory : History surface

    historiesDistinct : leftHistory ≡ rightHistory → ⊥

    samePresentObservation :
      observe surface leftHistory ≡ observe surface rightHistory

    choicesDiffer :
      choose surface leftHistory ≡ choose surface rightHistory → ⊥

open DistinctHistoriesSameObservationDifferentChoice public

historyChoiceNonFactorability :
  ∀ {surface : HistoryConditionedChoiceSurface} →
  DistinctHistoriesSameObservationDifferentChoice surface →
  NonFactor.NonFactorabilityWitness (observe surface) (choose surface)
historyChoiceNonFactorability witness =
  NonFactor.nonFactorabilityWitness
    (leftHistory witness)
    (rightHistory witness)
    (samePresentObservation witness)
    (choicesDiffer witness)

historySensitiveChoiceCannotDescendThroughPresentObservation :
  ∀ {surface : HistoryConditionedChoiceSurface} →
  DistinctHistoriesSameObservationDifferentChoice surface →
  NonFactor.FactorsThrough (observe surface) (choose surface) →
  ⊥
historySensitiveChoiceCannotDescendThroughPresentObservation witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (historyChoiceNonFactorability witness)

------------------------------------------------------------------------
-- Pattern-mediated form.
--
-- This witnesses the stronger architecture
--
--   history -> pattern -> present choice
--
-- while keeping the coarse observation as an independent projection.  The
-- theorem does not assume that every pattern difference changes choice; that
-- application-specific separation is carried by the concrete witness.
------------------------------------------------------------------------

record PatternMediatedChoiceWitness
    (surface : HistoryConditionedChoiceSurface) : Set where
  field
    leftHistory : History surface
    rightHistory : History surface

    sameObservation :
      observe surface leftHistory ≡ observe surface rightHistory

    patternsDiffer :
      patternOf surface leftHistory ≡ patternOf surface rightHistory → ⊥

    choicesDiffer :
      choose surface leftHistory ≡ choose surface rightHistory → ⊥

open PatternMediatedChoiceWitness public

patternMediatedChoiceCannotDescendThroughObservation :
  ∀ {surface : HistoryConditionedChoiceSurface} →
  PatternMediatedChoiceWitness surface →
  NonFactor.FactorsThrough (observe surface) (choose surface) →
  ⊥
patternMediatedChoiceCannotDescendThroughObservation witness factor =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (PatternMediatedChoiceWitness.leftHistory witness)
      (PatternMediatedChoiceWitness.rightHistory witness)
      (PatternMediatedChoiceWitness.sameObservation witness)
      (PatternMediatedChoiceWitness.choicesDiffer witness))
    factor

------------------------------------------------------------------------
-- Future-cone code.
--
-- A full powerset-valued reachable set would unnecessarily force universe and
-- extensional-equality commitments into the generic core.  Instead the owner
-- permits any exact application-supplied code for a history-conditioned future
-- cone.  Different codes at one coarse observation are already enough to prove
-- that the coarse present state is not future-sufficient.
------------------------------------------------------------------------

record HistoryConditionedFutureConeSurface : Set₁ where
  field
    History : Set
    Observation : Set
    FutureConeCode : Set

    observe : History → Observation
    futureCone : History → FutureConeCode

    futureReading : String

open HistoryConditionedFutureConeSurface public

record SameObservationDifferentFutureCone
    (surface : HistoryConditionedFutureConeSurface) : Set where
  field
    leftHistory : HistoryConditionedFutureConeSurface.History surface
    rightHistory : HistoryConditionedFutureConeSurface.History surface

    sameObservation :
      HistoryConditionedFutureConeSurface.observe surface leftHistory
      ≡ HistoryConditionedFutureConeSurface.observe surface rightHistory

    futureConesDiffer :
      HistoryConditionedFutureConeSurface.futureCone surface leftHistory
      ≡ HistoryConditionedFutureConeSurface.futureCone surface rightHistory → ⊥

open SameObservationDifferentFutureCone public

futureConeCannotDescendThroughPresentObservation :
  ∀ {surface : HistoryConditionedFutureConeSurface} →
  SameObservationDifferentFutureCone surface →
  NonFactor.FactorsThrough
    (HistoryConditionedFutureConeSurface.observe surface)
    (HistoryConditionedFutureConeSurface.futureCone surface) →
  ⊥
futureConeCannotDescendThroughPresentObservation witness =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    (NonFactor.nonFactorabilityWitness
      (SameObservationDifferentFutureCone.leftHistory witness)
      (SameObservationDifferentFutureCone.rightHistory witness)
      (SameObservationDifferentFutureCone.sameObservation witness)
      (SameObservationDifferentFutureCone.futureConesDiffer witness))

------------------------------------------------------------------------
-- Small exact specimen.
------------------------------------------------------------------------

data ToyHistory : Set where
  historyAlpha historyBeta : ToyHistory

data ToyObservation : Set where
  sameNow : ToyObservation

data ToyPattern : Set where
  patternAlpha patternBeta : ToyPattern

data ToyChoice : Set where
  continueAlpha continueBeta : ToyChoice

data ToyFutureCone : Set where
  alphaCone betaCone : ToyFutureCone

toyChoiceSurface : HistoryConditionedChoiceSurface
toyChoiceSurface =
  record
    { History = ToyHistory
    ; Observation = ToyObservation
    ; Pattern = ToyPattern
    ; Choice = ToyChoice
    ; observe = λ _ → sameNow
    ; patternOf = λ
        { historyAlpha → patternAlpha
        ; historyBeta → patternBeta
        }
    ; choose = λ
        { historyAlpha → continueAlpha
        ; historyBeta → continueBeta
        }
    ; historyReading =
        "Two histories may share one present projection while retaining different relational patterns and motivating different present choices."
    }

canonicalToyChoiceWitness :
  DistinctHistoriesSameObservationDifferentChoice toyChoiceSurface
canonicalToyChoiceWitness =
  record
    { leftHistory = historyAlpha
    ; rightHistory = historyBeta
    ; historiesDistinct = λ ()
    ; samePresentObservation = refl
    ; choicesDiffer = λ ()
    }

toyFutureConeSurface : HistoryConditionedFutureConeSurface
toyFutureConeSurface =
  record
    { History = ToyHistory
    ; Observation = ToyObservation
    ; FutureConeCode = ToyFutureCone
    ; observe = λ _ → sameNow
    ; futureCone = λ
        { historyAlpha → alphaCone
        ; historyBeta → betaCone
        }
    ; futureReading =
        "The same coarse present observation can hide histories with different coded continuation spaces."
    }

canonicalToyFutureConeWitness :
  SameObservationDifferentFutureCone toyFutureConeSurface
canonicalToyFutureConeWitness =
  record
    { leftHistory = historyAlpha
    ; rightHistory = historyBeta
    ; sameObservation = refl
    ; futureConesDiffer = λ ()
    }

record HistoryConditionedChoiceBoundary : Set where
  constructor historyConditionedChoiceBoundary
  field
    historyBearingAutomaticallyMeansPathDependent : Bool
    historyBearingAutomaticallyMeansPathDependentIsFalse :
      historyBearingAutomaticallyMeansPathDependent ≡ false

    samePresentObservationImpliesSameChoice : Bool
    samePresentObservationImpliesSameChoiceIsFalse :
      samePresentObservationImpliesSameChoice ≡ false

    samePresentObservationImpliesSameFutureCone : Bool
    samePresentObservationImpliesSameFutureConeIsFalse :
      samePresentObservationImpliesSameFutureCone ≡ false

    historySensitiveChoiceRequiresUniqueMicroscopicHistory : Bool
    historySensitiveChoiceRequiresUniqueMicroscopicHistoryIsFalse :
      historySensitiveChoiceRequiresUniqueMicroscopicHistory ≡ false

canonicalHistoryConditionedChoiceBoundary : HistoryConditionedChoiceBoundary
canonicalHistoryConditionedChoiceBoundary =
  historyConditionedChoiceBoundary
    false refl
    false refl
    false refl
    false refl
