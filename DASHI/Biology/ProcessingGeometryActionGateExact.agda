module DASHI.Biology.ProcessingGeometryActionGateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeurotypeProcessingGeometryExact as Processing

------------------------------------------------------------------------
-- PROCESSING GEOMETRY -> ACTION-GATE FUNCTIONAL
--
-- `NeurotypeProcessingGeometryExact` deliberately made latency an observer of a
-- richer multiaxial processing state.  This module is the next operational
-- step: selected processing coordinates now affect a finite action gate.
--
-- The map is a synthetic theorem specimen, not an empirical clinical model.
-- Its purpose is to prove that identical latency can hide different action
-- accessibility, and that action accessibility need not induce a global
-- ordering of cognitive capacity.
------------------------------------------------------------------------

data ProcessingAction : Set where
  rapidReorient sustainedRuleAnalysis remainUnderLoad : ProcessingAction

processingActionAvailable :
  Processing.ProcessingGeometry →
  Processing.SensoryContext →
  ProcessingAction → Bool
processingActionAvailable geometry context rapidReorient
  with Processing.switching geometry
... | Processing.lowSwitchCost = true
... | Processing.highSwitchCost = false
processingActionAvailable geometry context sustainedRuleAnalysis
  with Processing.depth geometry | Processing.ruleSearch geometry
... | Processing.persistentDeepPass | Processing.explicitRuleSearch = true
... | Processing.persistentDeepPass | Processing.mixedRuleSearch = true
... | _ | _ = false
processingActionAvailable geometry Processing.quietContext remainUnderLoad = true
processingActionAvailable geometry Processing.denseContext remainUnderLoad
  with Processing.sensoryBandwidth geometry
... | Processing.selectiveBandwidth = true
... | Processing.wideBandwidth = false
... | Processing.variableBandwidth = false

------------------------------------------------------------------------
-- Same latency, different gate.
------------------------------------------------------------------------

sameLatencyLowerSwitchGeometry : Processing.ProcessingGeometry
sameLatencyLowerSwitchGeometry =
  Processing.processingGeometry
    Processing.fineResolution
    Processing.narrowSearch
    Processing.persistentDeepPass
    Processing.detailRetainingIntegration
    Processing.highEvidenceCommit
    Processing.lowSwitchCost
    Processing.explicitRuleSearch
    Processing.wideBandwidth
    Processing.mixedInteroceptiveProfile

sameLatencyAsDeepRuleGeometry :
  Processing.latencyObserver Processing.deepRuleGeometry
  ≡ Processing.latencyObserver sameLatencyLowerSwitchGeometry
sameLatencyAsDeepRuleGeometry = refl

deepRuleRapidReorientClosed :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.quietContext
    rapidReorient
  ≡ false
deepRuleRapidReorientClosed = refl

lowerSwitchRapidReorientOpen :
  processingActionAvailable
    sameLatencyLowerSwitchGeometry
    Processing.quietContext
    rapidReorient
  ≡ true
lowerSwitchRapidReorientOpen = refl

sameLatencyDoesNotDetermineRapidReorientGate :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.quietContext
    rapidReorient
  ≡ processingActionAvailable
      sameLatencyLowerSwitchGeometry
      Processing.quietContext
      rapidReorient
  → ⊥
sameLatencyDoesNotDetermineRapidReorientGate ()

------------------------------------------------------------------------
-- The same geometry can also have action-specific strengths/constraints.
-- This blocks turning one closed gate into a global capacity ordering.
------------------------------------------------------------------------

deepRuleSustainedAnalysisOpen :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.quietContext
    sustainedRuleAnalysis
  ≡ true
deepRuleSustainedAnalysisOpen = refl

wideBandwidthDenseRemainClosed :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.denseContext
    remainUnderLoad
  ≡ false
wideBandwidthDenseRemainClosed = refl

wideBandwidthQuietRemainOpen :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.quietContext
    remainUnderLoad
  ≡ true
wideBandwidthQuietRemainOpen = refl

sameGeometryDifferentSensoryContextCanChangeGate :
  processingActionAvailable
    Processing.deepRuleGeometry
    Processing.quietContext
    remainUnderLoad
  ≡ processingActionAvailable
      Processing.deepRuleGeometry
      Processing.denseContext
      remainUnderLoad
  → ⊥
sameGeometryDifferentSensoryContextCanChangeGate ()

------------------------------------------------------------------------
-- Fail-closed interpretation boundary.
------------------------------------------------------------------------

record ProcessingActionGateBoundary : Set where
  constructor processing-action-gate-boundary
  field
    latencyDeterminesActionAccessibility : Bool
    latencyDeterminesActionAccessibilityIsFalse :
      latencyDeterminesActionAccessibility ≡ false
    oneClosedGateImpliesGlobalLowerCapacity : Bool
    oneClosedGateImpliesGlobalLowerCapacityIsFalse :
      oneClosedGateImpliesGlobalLowerCapacity ≡ false
    sensoryContextMayChangeGateAtFixedGeometry : Bool
    sensoryContextMayChangeGateAtFixedGeometryIsTrue :
      sensoryContextMayChangeGateAtFixedGeometry ≡ true
    syntheticGateIsValidatedClinicalDecisionRule : Bool
    syntheticGateIsValidatedClinicalDecisionRuleIsFalse :
      syntheticGateIsValidatedClinicalDecisionRule ≡ false
    processingCoordinatesCanBeOperationalInputs : Bool
    processingCoordinatesCanBeOperationalInputsIsTrue :
      processingCoordinatesCanBeOperationalInputs ≡ true

canonicalProcessingActionGateBoundary : ProcessingActionGateBoundary
canonicalProcessingActionGateBoundary =
  processing-action-gate-boundary
    false refl
    false refl
    true refl
    false refl
    true refl
