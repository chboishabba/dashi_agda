module DASHI.Core.SequentialDiagnosisDebugLoopBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.SequentialPlannerPluralClosureBidiExact as Plural
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Backprop
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.DiagnosisExperimentPortfolioBidiExact as Portfolio
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform

------------------------------------------------------------------------
-- SEQUENTIAL PLAN -> RESULT -> DIAGNOSIS FIBRE -> DEBUG MOVE -> REVISED PLAN
------------------------------------------------------------------------

record DebuggableTerminalPlan : Set₁ where
  constructor debuggable-terminal-plan
  field
    terminalPlan :
      Planner.SequentialConsumerPlan
        (Reform.answer Reform.reformulatedQuestion)
        Reform.liveFibre
    liveDiagnoses : Diagnosis.DiagnosisFibre
    debugMove : Portfolio.SalientDebugMove liveDiagnoses

open DebuggableTerminalPlan public

canonicalDebuggableTerminal : DebuggableTerminalPlan
canonicalDebuggableTerminal =
  debuggable-terminal-plan
    Plural.reformulatedTerminalPlan
    Diagnosis.ambiguousDiagnosisFibre
    Portfolio.frameControlSalientMove

canonicalTerminalHasLiveDiagnosisAmbiguity :
  liveDiagnoses canonicalDebuggableTerminal Backprop.Backprop.modelConflict
canonicalTerminalHasLiveDiagnosisAmbiguity = tt

canonicalTerminalDebugMoveStrictlyNarrows :
  Diagnosis.DiagnosisSalientOn
    (Diagnosis.observation (Portfolio.move (debugMove canonicalDebuggableTerminal)))
    (liveDiagnoses canonicalDebuggableTerminal)
canonicalTerminalDebugMoveStrictlyNarrows =
  Portfolio.narrows (debugMove canonicalDebuggableTerminal)

------------------------------------------------------------------------
-- A terminal answer and a live diagnosis fibre coexist legitimately.
-- Terminal means 'enough for the declared consumer now', not 'all explanation
-- uncertainty has vanished forever'.
------------------------------------------------------------------------

data TerminalPlanRequiresEmptyDiagnosisFibre : Set where
data DebuggingRequiresReopenConsumerImmediately : Set where

theTerminalPlanMayCoexistWithDiagnosisAmbiguity :
  TerminalPlanRequiresEmptyDiagnosisFibre → ⊥
theTerminalPlanMayCoexistWithDiagnosisAmbiguity ()

debuggingNeedNotImmediatelyReopenConsumer :
  DebuggingRequiresReopenConsumerImmediately → ⊥
debuggingNeedNotImmediatelyReopenConsumer ()

record SequentialDiagnosisLoopBoundary : Set where
  constructor sequential-diagnosis-loop-boundary
  field
    terminalAndDiagnosisAmbiguityMayCoexist : Bool
    debugObservationSelectedAgainstDiagnosisFibre : Bool
    debugObservationMustImmediatelyReopenConsumer : Bool
    posteriorDiagnosisMayGuideLaterRevision : Bool

canonicalSequentialDiagnosisLoopBoundary : SequentialDiagnosisLoopBoundary
canonicalSequentialDiagnosisLoopBoundary =
  sequential-diagnosis-loop-boundary true true false true
