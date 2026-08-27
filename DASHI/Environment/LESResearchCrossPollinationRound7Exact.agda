module DASHI.Environment.LESResearchCrossPollinationRound7Exact where

------------------------------------------------------------------------
-- ROUND 7: HISTORY-CONDITIONED CHOICE AND COARSE-STATE NON-DESCENT
--
-- This round connects the generic history-conditioned choice theorem to LES.
-- The environmental witness is deliberately generic and synthetic: it models
-- two management histories with the same coarse present summary but different
-- continuation structures.  It does not encode, quote, or identify any private
-- legal, commercial, agricultural, or family matter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.RelationalTensionCompressionExact as Tension
import DASHI.Environment.EcologicalKnowledge as Knowledge
import DASHI.Environment.LESResearchCrossPollinationExact as LES

------------------------------------------------------------------------
-- LES already records path dependence / hysteresis as an open research gap.
-- This module supplies an exact logical interface and finite non-descent
-- witness; it does not claim to close the quantitative environmental problem.
------------------------------------------------------------------------

lesPathDependenceGapIsExplicitlyOpen :
  LES.pathDependenceAndHysteresisStillRequired
    LES.canonicalLESResearchGapBoundary
  ≡ true
lesPathDependenceGapIsExplicitlyOpen = refl

------------------------------------------------------------------------
-- Generic environmental history specimen.
------------------------------------------------------------------------

data ManagementHistory : Set where
  shortHorizonConfiguration longHorizonConfiguration : ManagementHistory

data CoarsePresentSummary : Set where
  sameCurrentSuitabilitySummary : CoarsePresentSummary

data RelationalPattern : Set where
  readilyReconfigurablePattern committedLongHorizonPattern : RelationalPattern

data PlanningChoice : Set where
  rapidReconfigurationChoice stagedTransitionChoice : PlanningChoice

data ContinuationConeCode : Set where
  rapidBranchingCone delayedTransitionCone : ContinuationConeCode

observeManagementHistory : ManagementHistory → CoarsePresentSummary
observeManagementHistory _ = sameCurrentSuitabilitySummary

patternOfManagementHistory : ManagementHistory → RelationalPattern
patternOfManagementHistory shortHorizonConfiguration = readilyReconfigurablePattern
patternOfManagementHistory longHorizonConfiguration = committedLongHorizonPattern

choiceForManagementHistory : ManagementHistory → PlanningChoice
choiceForManagementHistory shortHorizonConfiguration = rapidReconfigurationChoice
choiceForManagementHistory longHorizonConfiguration = stagedTransitionChoice

futureConeForManagementHistory : ManagementHistory → ContinuationConeCode
futureConeForManagementHistory shortHorizonConfiguration = rapidBranchingCone
futureConeForManagementHistory longHorizonConfiguration = delayedTransitionCone

lesHistoryChoiceSurface : HistoryChoice.HistoryConditionedChoiceSurface
lesHistoryChoiceSurface =
  record
    { History = ManagementHistory
    ; Observation = CoarsePresentSummary
    ; Pattern = RelationalPattern
    ; Choice = PlanningChoice
    ; observe = observeManagementHistory
    ; patternOf = patternOfManagementHistory
    ; choose = choiceForManagementHistory
    ; historyReading =
        "LES planning can retain management history when the same current suitability summary hides different relational patterns and therefore different present planning choices."
    }

lesHistoryChoiceWitness :
  HistoryChoice.DistinctHistoriesSameObservationDifferentChoice
    lesHistoryChoiceSurface
lesHistoryChoiceWitness =
  record
    { leftHistory = shortHorizonConfiguration
    ; rightHistory = longHorizonConfiguration
    ; historiesDistinct = λ ()
    ; samePresentObservation = refl
    ; choicesDiffer = λ ()
    }

lesChoiceCannotDescendThroughCoarsePresentSummary :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    observeManagementHistory choiceForManagementHistory → ⊥
lesChoiceCannotDescendThroughCoarsePresentSummary =
  HistoryChoice.historySensitiveChoiceCannotDescendThroughPresentObservation
    lesHistoryChoiceWitness

lesFutureConeSurface : HistoryChoice.HistoryConditionedFutureConeSurface
lesFutureConeSurface =
  record
    { History = ManagementHistory
    ; Observation = CoarsePresentSummary
    ; FutureConeCode = ContinuationConeCode
    ; observe = observeManagementHistory
    ; futureCone = futureConeForManagementHistory
    ; futureReading =
        "A coarse current environmental summary need not determine the continuation cone when prior commitments differ."
    }

lesFutureConeWitness :
  HistoryChoice.SameObservationDifferentFutureCone lesFutureConeSurface
lesFutureConeWitness =
  record
    { leftHistory = shortHorizonConfiguration
    ; rightHistory = longHorizonConfiguration
    ; sameObservation = refl
    ; futureConesDiffer = λ ()
    }

------------------------------------------------------------------------
-- LES ecological-knowledge boundary already carries the local-vs-global
-- absence warning needed by the coarse-projection story.
------------------------------------------------------------------------

lesKnowledgeAbsenceIsNotEvidenceOfAbsence :
  Knowledge.absenceOfEntryIsNotEvidenceOfAbsence
    Knowledge.canonicalKnowledgeBoundary
  ≡ true
lesKnowledgeAbsenceIsNotEvidenceOfAbsence = refl

localFalseDoesNotPromoteToGlobalFalse :
  Tension.FalseEverywhereWitness → ⊥
localFalseDoesNotPromoteToGlobalFalse =
  Tension.falseHereDoesNotEstablishFalseEverywhere

------------------------------------------------------------------------
-- Boundary: this is a formal planning obstruction, not a fitted model.
------------------------------------------------------------------------

record LESRound7Boundary : Set where
  constructor lesRound7Boundary
  field
    sameCurrentSummaryCanHideDifferentHistories : Bool
    sameCurrentSummaryCanHideDifferentChoices : Bool
    sameCurrentSummaryCanHideDifferentContinuationCones : Bool
    historyBearingAloneProvesPathDependence : Bool
    finiteWitnessIsEmpiricalEnvironmentalEffectSize : Bool
    privateCaseFactsEncoded : Bool

canonicalLESRound7Boundary : LESRound7Boundary
canonicalLESRound7Boundary =
  lesRound7Boundary
    true
    true
    true
    false
    false
    false
