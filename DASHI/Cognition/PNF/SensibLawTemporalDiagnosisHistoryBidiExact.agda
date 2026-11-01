module DASHI.Cognition.PNF.SensibLawTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawDiagnosisRepairSchedulerBidiExact as Law
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection

------------------------------------------------------------------------
-- SENSIBLAW REPAIR WITH TEMPORAL / APPEND-ONLY DIAGNOSIS HISTORY
------------------------------------------------------------------------

reactivatedClassificationFrameConflictRoutesToRechart :
  Law.legalRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
reactivatedClassificationFrameConflictRoutesToRechart = refl

priorClassificationEliminationStillAuditable :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorClassificationEliminationStillAuditable =
  Temporal.priorEliminationStillPresentAfterReactivation

frameInspectionMayBecomeSalientAgain :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Projection.liveProjection Projection.afterReactivationBundle)
frameInspectionMayBecomeSalientAgain =
  Recalibration.frameCheckSalientAfterReactivation

authorityConflictStillNeedsAuthorityReceipt :
  Law.legalRevision Outcome.authorityMismatch ≡ Revision.seekAuthorityReceipt
authorityConflictStillNeedsAuthorityReceipt =
  Law.authorityMismatchRoutesToAuthorityReceipt

data ReactivatedLegalDiagnosisChangesHistoricalHolding : Set where
data ReactivatedFrameConflictCreatesAuthority : Set where

temporalReactivationDoesNotRewriteHistoricalHolding :
  ReactivatedLegalDiagnosisChangesHistoricalHolding → ⊥
temporalReactivationDoesNotRewriteHistoricalHolding ()

reactivatedFrameConflictDoesNotCreateAuthority :
  ReactivatedFrameConflictCreatesAuthority → ⊥
reactivatedFrameConflictDoesNotCreateAuthority ()

record SensibLawTemporalDiagnosisBoundary : Set where
  constructor sensiblaw-temporal-diagnosis-boundary
  field
    legalDiagnosisMayReactivate : Bool
    earlierEliminationRemainsAuditable : Bool
    frameDebuggerMayBecomeSalientAgain : Bool
    reactivationRewritesHistoricalHolding : Bool
    reactivationCreatesAuthority : Bool

canonicalSensibLawTemporalDiagnosisBoundary : SensibLawTemporalDiagnosisBoundary
canonicalSensibLawTemporalDiagnosisBoundary =
  sensiblaw-temporal-diagnosis-boundary true true true false false
