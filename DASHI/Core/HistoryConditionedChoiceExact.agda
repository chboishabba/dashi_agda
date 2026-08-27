module DASHI.Core.HistoryConditionedChoiceExact where

------------------------------------------------------------------------
-- HISTORY-CONDITIONED CHOICE / FUTURE-CONE NON-FACTORABILITY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- Draft PR #621 independently introduced this theorem shape while formalising
-- coupled trajectories: a coarse present observation need not determine either
-- the choice selected from a history or the history-conditioned future cone.
-- PR #606 supplies the same structural pressure through history-deformed gates,
-- PR #613 through retained trajectory residue, and PR #624 through trading
-- history/optionality.  This Core owner extracts the common mathematics without
-- importing any draft branch or domain semantics.
--
-- The key distinction is:
--
--   same present observation != same retained history pattern
--                            != same choice
--                            != same reachable future cone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- History-sensitive choice surface.
------------------------------------------------------------------------

record HistoryConditionedChoiceSurface : Set₁ where
  constructor history-conditioned-choice-surface
  field
    History Observation Pattern Choice : Set
    observe : History → Observation
    patternOf : History → Pattern
    choose : History → Choice
    historyReading : String

open HistoryConditionedChoiceSurface public

record SameObservationDifferentChoice
    (surface : HistoryConditionedChoiceSurface) : Set where
  constructor same-observation-different-choice
  field
    leftHistory rightHistory : History surface
    sameObservation :
      observe surface leftHistory ≡ observe surface rightHistory
    choicesDiffer :
      choose surface leftHistory ≡ choose surface rightHistory → ⊥

open SameObservationDifferentChoice public

choiceNonfactorability :
  {surface : HistoryConditionedChoiceSurface} →
  SameObservationDifferentChoice surface →
  NF.NonFactorabilityWitness (observe surface) (choose surface)
choiceNonfactorability witness =
  NF.nonFactorabilityWitness
    (leftHistory witness)
    (rightHistory witness)
    (sameObservation witness)
    (choicesDiffer witness)

presentObservationCannotDetermineChoice :
  {surface : HistoryConditionedChoiceSurface} →
  SameObservationDifferentChoice surface →
  NF.FactorsThrough (observe surface) (choose surface) →
  ⊥
presentObservationCannotDetermineChoice witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (choiceNonfactorability witness)

postprocessedPresentCannotDetermineChoice :
  {surface : HistoryConditionedChoiceSurface} →
  ∀ {Chart : Set} →
  (rechart : Observation surface → Chart) →
  SameObservationDifferentChoice surface →
  NF.FactorsThrough
    (λ history → rechart (observe surface history))
    (choose surface) →
  ⊥
postprocessedPresentCannotDetermineChoice rechart witness =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (choiceNonfactorability witness)

------------------------------------------------------------------------
-- Pattern split: useful when the application wants to retain an explicit
-- history summary rather than a unique microscopic trajectory.
------------------------------------------------------------------------

record SameObservationDifferentPattern
    (surface : HistoryConditionedChoiceSurface) : Set where
  constructor same-observation-different-pattern
  field
    patternLeft patternRight : History surface
    patternSameObservation :
      observe surface patternLeft ≡ observe surface patternRight
    patternsDiffer :
      patternOf surface patternLeft ≡ patternOf surface patternRight → ⊥

open SameObservationDifferentPattern public

patternNonfactorability :
  {surface : HistoryConditionedChoiceSurface} →
  SameObservationDifferentPattern surface →
  NF.NonFactorabilityWitness (observe surface) (patternOf surface)
patternNonfactorability witness =
  NF.nonFactorabilityWitness
    (patternLeft witness)
    (patternRight witness)
    (patternSameObservation witness)
    (patternsDiffer witness)

presentObservationCannotDeterminePattern :
  {surface : HistoryConditionedChoiceSurface} →
  SameObservationDifferentPattern surface →
  NF.FactorsThrough (observe surface) (patternOf surface) →
  ⊥
presentObservationCannotDeterminePattern witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (patternNonfactorability witness)

------------------------------------------------------------------------
-- Future-cone code.
--
-- Applications may use any exact code for reachable/admissible future options;
-- the generic theorem does not force powerset equality or a particular
-- reachability representation into Core.
------------------------------------------------------------------------

record HistoryConditionedFutureConeSurface : Set₁ where
  constructor history-conditioned-future-cone-surface
  field
    FutureHistory FutureObservation FutureConeCode : Set
    observeFutureHistory : FutureHistory → FutureObservation
    futureCone : FutureHistory → FutureConeCode
    futureReading : String

open HistoryConditionedFutureConeSurface public

record SameObservationDifferentFutureCone
    (surface : HistoryConditionedFutureConeSurface) : Set where
  constructor same-observation-different-future-cone
  field
    futureLeft futureRight : FutureHistory surface
    futureSameObservation :
      observeFutureHistory surface futureLeft
      ≡ observeFutureHistory surface futureRight
    futureConesDiffer :
      futureCone surface futureLeft
      ≡ futureCone surface futureRight → ⊥

open SameObservationDifferentFutureCone public

futureConeNonfactorability :
  {surface : HistoryConditionedFutureConeSurface} →
  SameObservationDifferentFutureCone surface →
  NF.NonFactorabilityWitness
    (observeFutureHistory surface)
    (futureCone surface)
futureConeNonfactorability witness =
  NF.nonFactorabilityWitness
    (futureLeft witness)
    (futureRight witness)
    (futureSameObservation witness)
    (futureConesDiffer witness)

presentObservationCannotDetermineFutureCone :
  {surface : HistoryConditionedFutureConeSurface} →
  SameObservationDifferentFutureCone surface →
  NF.FactorsThrough
    (observeFutureHistory surface)
    (futureCone surface) →
  ⊥
presentObservationCannotDetermineFutureCone witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (futureConeNonfactorability witness)

postprocessedPresentCannotDetermineFutureCone :
  {surface : HistoryConditionedFutureConeSurface} →
  ∀ {Chart : Set} →
  (rechart : FutureObservation surface → Chart) →
  SameObservationDifferentFutureCone surface →
  NF.FactorsThrough
    (λ history → rechart (observeFutureHistory surface history))
    (futureCone surface) →
  ⊥
postprocessedPresentCannotDetermineFutureCone rechart witness =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart
    (futureConeNonfactorability witness)

------------------------------------------------------------------------
-- Exact finite regression.
------------------------------------------------------------------------

data ToyHistory : Set where
  historyAlpha historyBeta : ToyHistory

data ToyObservation : Set where
  sameNow : ToyObservation

data ToyPattern : Set where
  alphaPattern betaPattern : ToyPattern

data ToyChoice : Set where
  alphaChoice betaChoice : ToyChoice

data ToyFutureCone : Set where
  alphaCone betaCone : ToyFutureCone

toyChoiceSurface : HistoryConditionedChoiceSurface
toyChoiceSurface =
  history-conditioned-choice-surface
    ToyHistory ToyObservation ToyPattern ToyChoice
    (λ _ → sameNow)
    (λ { historyAlpha → alphaPattern ; historyBeta → betaPattern })
    (λ { historyAlpha → alphaChoice ; historyBeta → betaChoice })
    "Two histories share one present projection while retaining different patterns and choices."

toyChoiceWitness : SameObservationDifferentChoice toyChoiceSurface
toyChoiceWitness =
  same-observation-different-choice historyAlpha historyBeta refl (λ ())

toyPatternWitness : SameObservationDifferentPattern toyChoiceSurface
toyPatternWitness =
  same-observation-different-pattern historyAlpha historyBeta refl (λ ())

toyFutureSurface : HistoryConditionedFutureConeSurface
toyFutureSurface =
  history-conditioned-future-cone-surface
    ToyHistory ToyObservation ToyFutureCone
    (λ _ → sameNow)
    (λ { historyAlpha → alphaCone ; historyBeta → betaCone })
    "The same coarse present observation can hide histories with different coded continuation spaces."

toyFutureWitness : SameObservationDifferentFutureCone toyFutureSurface
toyFutureWitness =
  same-observation-different-future-cone historyAlpha historyBeta refl (λ ())

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record HistoryConditionedChoiceBoundary : Set where
  constructor history-conditioned-choice-boundary
  field
    samePresentObservationImpliesSameHistoryPattern : Bool
    samePresentObservationImpliesSameHistoryPatternIsFalse :
      samePresentObservationImpliesSameHistoryPattern ≡ false

    samePresentObservationImpliesSameChoice : Bool
    samePresentObservationImpliesSameChoiceIsFalse :
      samePresentObservationImpliesSameChoice ≡ false

    samePresentObservationImpliesSameFutureCone : Bool
    samePresentObservationImpliesSameFutureConeIsFalse :
      samePresentObservationImpliesSameFutureCone ≡ false

    postprocessingPresentObservationRecoversErasedHistory : Bool
    postprocessingPresentObservationRecoversErasedHistoryIsFalse :
      postprocessingPresentObservationRecoversErasedHistory ≡ false

    historySensitivityRequiresUniqueMicroscopicHistory : Bool
    historySensitivityRequiresUniqueMicroscopicHistoryIsFalse :
      historySensitivityRequiresUniqueMicroscopicHistory ≡ false

canonicalHistoryConditionedChoiceBoundary : HistoryConditionedChoiceBoundary
canonicalHistoryConditionedChoiceBoundary =
  history-conditioned-choice-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
