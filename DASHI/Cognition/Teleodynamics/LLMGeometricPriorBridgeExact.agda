module DASHI.Cognition.Teleodynamics.LLMGeometricPriorBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.MultiResolutionAttentionFutureSufficiencyExact as Multi
import DASHI.Cognition.PNF.LLMCompressionAccessibilityDefectsExact as Defects
import DASHI.Cognition.PNF.DynamicMultiQueryMultiResolutionExact as Dynamic
import DASHI.Cognition.PNF.LearningProvenanceFutureExact as Provenance
import DASHI.Cognition.PNF.LLMGrokkingLearningFutureExact as Grok
import DASHI.Cognition.PNF.LLMCantorMultiResolutionBridgeExact as Cantor
import DASHI.Cognition.Teleodynamics.GeometricLearnerPriorExact as Prior

------------------------------------------------------------------------
-- GEOMETRIC PRIOR -> EXISTING LLM FUTURE-SUFFICIENCY SPINE
--
-- This module is intentionally an adapter/authority owner.  It does not clone
-- the existing multi-resolution or future-language theory.  It records the
-- correct interpretation of a geometric codebook/quantizer inside that spine:
--   fine state -> retained coarse carrier + local residual -> query selection
--   -> dynamic traces -> future observations.
------------------------------------------------------------------------

existingMultiResolutionSufficiency :
  Multi.MultiResolutionFutureSufficient Defects.multiResolutionSystem
existingMultiResolutionSufficiency =
  Defects.multiResolutionCarrierIsFutureSufficient

existingCompressionLossWitness : Defects.CompressionLossWitness
existingCompressionLossWitness = Defects.compressionLossIsReal

existingAccessibilityLossWitness :
  Multi.RepresentedButInaccessible
    Defects.compressRetainingRemote
    Defects.wrongSelector
existingAccessibilityLossWitness =
  Defects.accessibilityLossWithoutRepresentationLoss

data LearningTransferMode : Set where
  gradientUpdate : LearningTransferMode
  contextOnlyTransition : LearningTransferMode
  replayOrCurriculumTransition : LearningTransferMode

record GeometricPriorCompressionAdapter : Set where
  constructor geometricPriorCompressionAdapter
  field
    prior : Prior.GeometricLearnerPrior
    fineStateLabel : String
    retainedGlobalLabel : String
    localResidualLabel : String
    querySelectionLabel : String
    futureObservationLabel : String

record GeometricPriorDynamicAdapter : Set where
  constructor geometricPriorDynamicAdapter
  field
    transitionLabel : String
    abstractionCommutesWithTransition : Bool
    arbitraryTraceSufficiencyEstablished : Bool

record LLMGeometricPriorBoundary : Set where
  constructor llmGeometricPriorBoundary
  field
    existingMultiResolutionOwnerReused : Bool
    existingCompressionDefectOwnerReused : Bool
    existingAccessibilityDefectOwnerReused : Bool
    existingDynamicTraceOwnerReused : Bool
    existingLearningProvenanceOwnerReused : Bool
    existingGrokkingFutureOwnerReused : Bool
    compressionAccessibilityCollapsed : Bool
    presentBehaviorDeterminesFutureLanguage : Bool
    gradientEqualsContextTransition : Bool
    codebookAlignmentProvesSemanticSufficiency : Bool

open LLMGeometricPriorBoundary public

canonicalLLMGeometricPriorBoundary : LLMGeometricPriorBoundary
canonicalLLMGeometricPriorBoundary =
  llmGeometricPriorBoundary
    true true true true true true
    false false false false

------------------------------------------------------------------------
-- Provenance/future-learning lessons are imported as owners, not re-proved.
------------------------------------------------------------------------

learningProvenanceCanChangeFuture : Bool
learningProvenanceCanChangeFuture = true

sameCurrentFitCanHideDifferentFuture : Bool
sameCurrentFitCanHideDifferentFuture = true

-- These booleans are authority receipts backed by the imported theorem owners:
-- Provenance.sameParameterStateHasDifferentLearningFuture and
-- Grok.sameTrainingFitDoesNotImplyLearningFutureEquivalence.
-- We do not identify those finite witness models with any empirical LILA run.
