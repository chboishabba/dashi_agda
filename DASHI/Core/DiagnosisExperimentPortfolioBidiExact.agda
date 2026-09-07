module DASHI.Core.DiagnosisExperimentPortfolioBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Sequential

------------------------------------------------------------------------
-- DIAGNOSIS-CONDITIONED DEBUGGING PORTFOLIO
--
-- A debugging move is chosen against the current diagnosis fibre.  The move
-- does not itself select a conclusion; it either narrows the diagnosis fibre or
-- leaves it unchanged, after which a revision action may be selected only for
-- the still-live diagnosed dependency.
------------------------------------------------------------------------

data DebugMoveKind : Set where
  repeatObservation
  frameControl
  premiseAudit
  ruleAudit
  modelPerturbation
  consumerReformulationCheck
  provenanceAudit
  authorityAudit
  : DebugMoveKind

record DebugMove : Set₁ where
  constructor debug-move
  field
    kind : DebugMoveKind
    observation : Diagnosis.DebugObservation
    admitted : Set
    admissionReceipt : admitted
    moveReference : String

open DebugMove public

record SalientDebugMove
    (prior : Diagnosis.DiagnosisFibre) : Set₁ where
  constructor salient-debug-move
  field
    move : DebugMove
    narrows : Diagnosis.DiagnosisSalientOn (observation move) prior
    selectedRevisionIfResolved : Backprop.OutcomeDiagnosis → Sequential.RevisionAction
    revisionReference : String

open SalientDebugMove public

frameControlMove : DebugMove
frameControlMove =
  debug-move frameControl Diagnosis.smallFrameCheck ⊤ tt
    "frame-orientation control admitted for synthetic diagnosis calibration"

frameControlSalientMove :
  SalientDebugMove Diagnosis.ambiguousDiagnosisFibre
frameControlSalientMove =
  salient-debug-move
    frameControlMove
    Diagnosis.smallFrameCheckIsSalient
    revision
    "if later evidence resolves the diagnosis, map it to the corresponding typed revision action"
  where
    revision : Backprop.OutcomeDiagnosis → Sequential.RevisionAction
    revision Backprop.observationConflict = Sequential.reacquireObservation
    revision Backprop.frameConflict = Sequential.rechartRepresentation
    revision Backprop.premiseConflict = Sequential.inspectPremise
    revision Backprop.ruleConflict = Sequential.inspectRule
    revision Backprop.modelConflict = Sequential.reviseModel
    revision Backprop.consumerMismatch = Sequential.reformulateConsumer
    revision Backprop.provenanceConflict = Sequential.acquireIndependentProvenance
    revision Backprop.authorityMismatch = Sequential.seekAuthorityReceipt
    revision Backprop.insufficientResolution = Sequential.reacquireObservation

frameControlEliminatesFrameConflict :
  ¬ (Diagnosis.updateDiagnosisFibre
      Diagnosis.smallFrameCheck
      Diagnosis.ambiguousDiagnosisFibre
      Backprop.frameConflict)
frameControlEliminatesFrameConflict proof = proof

frameControlPreservesModelConflict :
  Diagnosis.updateDiagnosisFibre
    Diagnosis.smallFrameCheck
    Diagnosis.ambiguousDiagnosisFibre
    Backprop.modelConflict
frameControlPreservesModelConflict = tt

frameControlPreservesPremiseConflict :
  Diagnosis.updateDiagnosisFibre
    Diagnosis.smallFrameCheck
    Diagnosis.ambiguousDiagnosisFibre
    Backprop.premiseConflict
frameControlPreservesPremiseConflict = tt

------------------------------------------------------------------------
-- The posterior diagnosis fibre, not raw polarity, determines the next audit.
------------------------------------------------------------------------

data SalientDebugMoveCreatesConclusion : Set where
data EliminatedDiagnosisWasFalseInWorld : Set where
data DebugAdmissionCreatesActionAuthority : Set where

salientDebugMoveDoesNotCreateConclusion :
  SalientDebugMoveCreatesConclusion → ⊥
salientDebugMoveDoesNotCreateConclusion ()

eliminationDoesNotClaimWorldFalsehood : EliminatedDiagnosisWasFalseInWorld → ⊥
eliminationDoesNotClaimWorldFalsehood ()

debugAdmissionDoesNotCreateAuthority : DebugAdmissionCreatesActionAuthority → ⊥
debugAdmissionDoesNotCreateAuthority ()

record DiagnosisExperimentPortfolioBoundary : Set where
  constructor diagnosis-experiment-portfolio-boundary
  field
    debugMovesAreDiagnosisConditioned : Bool
    salienceMayNarrowWithoutResolving : Bool
    eliminatedDiagnosisMeansWorldFalse : Bool
    posteriorDiagnosisGuidesRevision : Bool
    debugMoveCreatesAuthority : Bool

canonicalDiagnosisExperimentPortfolioBoundary : DiagnosisExperimentPortfolioBoundary
canonicalDiagnosisExperimentPortfolioBoundary =
  diagnosis-experiment-portfolio-boundary true true false true false
