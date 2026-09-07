module DASHI.Core.ArgumentDiagnosisDebuggingBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome

------------------------------------------------------------------------
-- ARGUMENT DEBUGGING <-> DIAGNOSIS FIBRE
--
-- A counterargument need not select one failure mode.  Keep premise/evidence/
-- rule/model/frame explanations live until a response-specific inspection
-- separates them.
------------------------------------------------------------------------

argumentDiagnosisFibre : Diagnosis.DiagnosisFibre
argumentDiagnosisFibre Outcome.premiseConflict = ⊤
argumentDiagnosisFibre Outcome.observationConflict = ⊤
argumentDiagnosisFibre Outcome.ruleConflict = ⊤
argumentDiagnosisFibre Outcome.modelConflict = ⊤
argumentDiagnosisFibre Outcome.frameConflict = ⊤
argumentDiagnosisFibre _ = ⊥

responseDiagnosis : Response.ResponseKind → Outcome.OutcomeDiagnosis
responseDiagnosis Response.denyPremise = Outcome.premiseConflict
responseDiagnosis Response.challengeEvidence = Outcome.observationConflict
responseDiagnosis Response.challengeRule = Outcome.ruleConflict
responseDiagnosis Response.disputeCausation = Outcome.modelConflict
responseDiagnosis Response.disputeCharacterisation = Outcome.frameConflict
responseDiagnosis Response.addContext = Outcome.frameConflict
responseDiagnosis Response.alternativeExplanation = Outcome.modelConflict
responseDiagnosis Response.acceptWithQualification = Outcome.consumerMismatch
responseDiagnosis Response.suspendJudgement = Outcome.insufficientResolution

challengeEvidenceKeepsEvidenceDiagnosisTyped :
  responseDiagnosis Response.challengeEvidence ≡ Outcome.observationConflict
challengeEvidenceKeepsEvidenceDiagnosisTyped = refl

alternativeExplanationKeepsModelDiagnosisTyped :
  responseDiagnosis Response.alternativeExplanation ≡ Outcome.modelConflict
alternativeExplanationKeepsModelDiagnosisTyped = refl

frameControlCanBeUsefulBeforeChoosingArgumentFailure :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    Diagnosis.ambiguousDiagnosisFibre
frameControlCanBeUsefulBeforeChoosingArgumentFailure =
  Diagnosis.smallFrameCheckIsSalient

data CounterargumentIdentifiesUniqueFailure : Set where
data ResponseKindRefutesTarget : Set where

counterargumentNeedNotIdentifyUniqueFailure :
  CounterargumentIdentifiesUniqueFailure → ⊥
counterargumentNeedNotIdentifyUniqueFailure ()

responseKindDoesNotRefuteTarget : ResponseKindRefutesTarget → ⊥
responseKindDoesNotRefuteTarget ()

record ArgumentDiagnosisDebugBoundary : Set where
  constructor argument-diagnosis-debug-boundary
  field
    multipleFailureDiagnosesMayRemainLive : Bool
    responseKindCanTargetInspectionCoordinate : Bool
    counterargumentEqualsUniqueFailureDiagnosis : Bool
    diagnosisSalienceMayChooseNextInspection : Bool

canonicalArgumentDiagnosisDebugBoundary : ArgumentDiagnosisDebugBoundary
canonicalArgumentDiagnosisDebugBoundary =
  argument-diagnosis-debug-boundary true true false true
