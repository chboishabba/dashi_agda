module DASHI.Physics.Closure.TSFVHistoryConditionedChoiceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryConditionedChoiceExact as Choice
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Physics.Closure.TSFVBidirectionalCausticBridgeExact as Caustic

------------------------------------------------------------------------
-- HISTORY-CONDITIONED CONSUMER DOWNSTREAM OF THE CAUSTIC PROJECTION
--
-- PR #621 already proves that historyABC and historyACB are distinct while
-- sharing one focused coarse projection.  This bridge adds a deliberately
-- synthetic downstream choice consumer that distinguishes those histories.
-- It therefore proves the generic theorem shape:
--
--   same coarse present observation
--   + different fine histories
--   + different history-sensitive choices
--   => choice cannot factor through the coarse observation.
--
-- The choice labels below are logical witnesses only.  They are not photon
-- interventions, experimental recommendations, or a TSFV mechanism claim.
------------------------------------------------------------------------

data HistoryPattern : Set where
  abcPattern acbPattern otherPattern : HistoryPattern

data HistorySensitiveChoice : Set where
  continueABC continueACB deferChoice : HistorySensitiveChoice

historyPattern : History.History3 → HistoryPattern
historyPattern
  (History.configurationA , (History.configurationB , History.configurationC)) =
  abcPattern
historyPattern
  (History.configurationA , (History.configurationC , History.configurationB)) =
  acbPattern
historyPattern _ = otherPattern

historySensitiveChoice : History.History3 → HistorySensitiveChoice
historySensitiveChoice
  (History.configurationA , (History.configurationB , History.configurationC)) =
  continueABC
historySensitiveChoice
  (History.configurationA , (History.configurationC , History.configurationB)) =
  continueACB
historySensitiveChoice _ = deferChoice

causticHistoryChoiceSurface : Choice.HistoryConditionedChoiceSurface
causticHistoryChoiceSurface =
  record
    { History = History.History3
    ; Observation = Caustic.HistoryObservation
    ; Pattern = HistoryPattern
    ; Choice = HistorySensitiveChoice
    ; observe = Caustic.historyProjection
    ; patternOf = historyPattern
    ; choose = historySensitiveChoice
    ; historyReading =
        "Distinct admissible histories may share one coarse focused observation while retaining different fine patterns that a later history-sensitive consumer can use."
    }

abcAndAcbChoicesDiffer :
  historySensitiveChoice History.historyABC
  ≡ historySensitiveChoice History.historyACB → ⊥
abcAndAcbChoicesDiffer ()

causticSameObservationDifferentChoice :
  Choice.DistinctHistoriesSameObservationDifferentChoice
    causticHistoryChoiceSurface
causticSameObservationDifferentChoice =
  record
    { leftHistory = History.historyABC
    ; rightHistory = History.historyACB
    ; historiesDistinct = Caustic.historyABCAndACBAreDistinct
    ; samePresentObservation =
        Caustic.Caustic.sharedProjection Caustic.historyDistinctSharedProjection
    ; choicesDiffer = abcAndAcbChoicesDiffer
    }

causticProjectionInsufficientForHistorySensitiveChoice :
  NonFactor.FactorsThrough
    Caustic.historyProjection historySensitiveChoice → ⊥
causticProjectionInsufficientForHistorySensitiveChoice =
  Choice.historySensitiveChoiceCannotDescendThroughPresentObservation
    causticSameObservationDifferentChoice

record TSFVHistoryConditionedChoiceBoundary : Set where
  constructor tsfvHistoryConditionedChoiceBoundary
  field
    sameCausticProjectionForcesSameDownstreamChoice : Bool
    sameCausticProjectionForcesSameDownstreamChoiceIsFalse :
      sameCausticProjectionForcesSameDownstreamChoice ≡ false

    syntheticChoiceIsPhotonExperimentResult : Bool
    syntheticChoiceIsPhotonExperimentResultIsFalse :
      syntheticChoiceIsPhotonExperimentResult ≡ false

    historyChoiceBridgeValidatesTSFVMechanism : Bool
    historyChoiceBridgeValidatesTSFVMechanismIsFalse :
      historyChoiceBridgeValidatesTSFVMechanism ≡ false

    bridgeReading : String

canonicalTSFVHistoryConditionedChoiceBoundary :
  TSFVHistoryConditionedChoiceBoundary
canonicalTSFVHistoryConditionedChoiceBoundary =
  tsfvHistoryConditionedChoiceBoundary
    false refl
    false refl
    false refl
    "The caustic projection may be sufficient for one observation while remaining insufficient for a later consumer whose decision depends on fine history; sufficiency is consumer-relative."
