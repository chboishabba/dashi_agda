module DASHI.Foundations.StageZeroToTwelveTransitionCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToTwelve as Stage

------------------------------------------------------------------------
-- Guarded transition topology for the conservative 0..12 extension.
--
-- This repeats the established non-linear 0..11 routes on the extended
-- carrier and adds exactly one new structural edge: 11 -> 12 opens the first
-- relation at the carried decimal scale.
------------------------------------------------------------------------

data GuardedStage012Edge :
  Stage.StageAtlasZeroToTwelve →
  Stage.StageAtlasZeroToTwelve →
  Set where
  instantiate : GuardedStage012Edge Stage.stage-0 Stage.stage-1
  openRelation : GuardedStage012Edge Stage.stage-1 Stage.stage-2
  articulateLocal : GuardedStage012Edge Stage.stage-2 Stage.stage-3
  exposeCounterframe : GuardedStage012Edge Stage.stage-3 Stage.stage-4
  preserveTetralemma : GuardedStage012Edge Stage.stage-4 Stage.stage-5
  arrestedTetralemma : GuardedStage012Edge Stage.stage-4 Stage.stage-1
  branchAfterDecision : GuardedStage012Edge Stage.stage-5 Stage.stage-6
  prematureLocalCollapse : GuardedStage012Edge Stage.stage-5 Stage.stage-3
  abandonAtDecision : GuardedStage012Edge Stage.stage-5 Stage.stage-0
  inspectSheetExchange : GuardedStage012Edge Stage.stage-6 Stage.stage-7
  reflexiveOscillation : GuardedStage012Edge Stage.stage-6 Stage.stage-6
  isolateResidual : GuardedStage012Edge Stage.stage-7 Stage.stage-8
  retainResidualInSynthesis : GuardedStage012Edge Stage.stage-8 Stage.stage-9
  systemicSelfLoop : GuardedStage012Edge Stage.stage-9 Stage.stage-9
  admitExternalCoordinate : GuardedStage012Edge Stage.stage-9 Stage.stage-10
  addFreshLocalUnit : GuardedStage012Edge Stage.stage-10 Stage.stage-11
  openCrossScaleRelation : GuardedStage012Edge Stage.stage-11 Stage.stage-12
  falseOverflowRestart : GuardedStage012Edge Stage.stage-10 Stage.stage-1

record GuardedStage012Transition : Set₁ where
  field
    source target : Stage.StageAtlasZeroToTwelve
    edge : GuardedStage012Edge source target
    requiredValuationDepth availableValuationDepth : Nat
    depthAdmissible : Bool
    memoryReceipt : String
    learningAdapterAvailable : Bool
    unresolvedResidualsRetained : Bool
    semanticAuthorityPromoted : Bool

canonicalStage11To12Transition : GuardedStage012Transition
canonicalStage11To12Transition = record
  { source = Stage.stage-11
  ; target = Stage.stage-12
  ; edge = openCrossScaleRelation
  ; requiredValuationDepth = 12
  ; availableValuationDepth = 12
  ; depthAdmissible = true
  ; memoryReceipt =
      "carried closure, fresh local predicate and prior residual provenance retained"
  ; learningAdapterAvailable = true
  ; unresolvedResidualsRetained = true
  ; semanticAuthorityPromoted = false
  }

record Stage012TransitionAuthorityBoundary : Set where
  field
    legacyNonlinearRoutesRetained : Bool
    stage11To12EdgeAvailable : Bool
    stage12ReachedByNumeralAlone : Bool
    valuationAndMemoryStillRequired : Bool
    stage12IsTerminal : Bool
    stage12ProvesSuccessfulAnalysis : Bool
    boundaryNote : String

canonicalStage012TransitionAuthorityBoundary :
  Stage012TransitionAuthorityBoundary
canonicalStage012TransitionAuthorityBoundary = record
  { legacyNonlinearRoutesRetained = true
  ; stage11To12EdgeAvailable = true
  ; stage12ReachedByNumeralAlone = false
  ; valuationAndMemoryStillRequired = true
  ; stage12IsTerminal = false
  ; stage12ProvesSuccessfulAnalysis = false
  ; boundaryNote =
      "Stage 12 extends the guarded chart by a cross-scale relation edge; loops, arrests, restarts, valuation, memory and residual conditions remain active."
  }
