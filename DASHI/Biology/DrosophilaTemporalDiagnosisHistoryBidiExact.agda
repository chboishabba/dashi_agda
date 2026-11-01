module DASHI.Biology.DrosophilaTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DrosophilaDiagnosisRepairSchedulerBidiExact as Fly
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection

------------------------------------------------------------------------
-- DROSOPHILA / SAME-TRIAL DIAGNOSIS HISTORY
--
-- The temporal fixture is methodological, not an empirical claim about a
-- particular experiment: a registration/frame diagnosis can be eliminated by
-- one control and later become live again under new evidence while the earlier
-- control and provenance remain in history.
------------------------------------------------------------------------

reactivatedRegistrationDiagnosisRoutesToRechart :
  Fly.flyRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
reactivatedRegistrationDiagnosisRoutesToRechart =
  Fly.registrationOrFrameConflictRequestsRechart

priorRegistrationEliminationStillAuditable :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorRegistrationEliminationStillAuditable =
  Temporal.priorEliminationStillPresentAfterReactivation

registrationControlMayBecomeSalientAgain :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Projection.liveProjection Projection.afterReactivationBundle)
registrationControlMayBecomeSalientAgain =
  Recalibration.frameCheckSalientAfterReactivation

provenanceConflictStillRequiresIndependentReplicationRoute :
  Fly.flyRevision Outcome.provenanceConflict
  ≡ Revision.acquireIndependentProvenance
provenanceConflictStillRequiresIndependentReplicationRoute =
  Fly.sameTrialProvenanceConflictRequestsIndependentReplication

data ReactivationMeansPriorBiologicalInterpretationWasOpposite : Set where
data ReactivationCreatesIndependentReplication : Set where

reactivationDoesNotMeanBiologicalOpposite :
  ReactivationMeansPriorBiologicalInterpretationWasOpposite → ⊥
reactivationDoesNotMeanBiologicalOpposite ()

reactivationDoesNotCreateIndependentReplication :
  ReactivationCreatesIndependentReplication → ⊥
reactivationDoesNotCreateIndependentReplication ()

record DrosophilaTemporalDiagnosisBoundary : Set where
  constructor drosophila-temporal-diagnosis-boundary
  field
    diagnosisMayReactivate : Bool
    earlierControlRemainsAuditable : Bool
    oldControlMayBecomeSalientAgain : Bool
    reactivationMeansBiologicalOpposite : Bool
    reactivationCreatesIndependentReplication : Bool

canonicalDrosophilaTemporalDiagnosisBoundary : DrosophilaTemporalDiagnosisBoundary
canonicalDrosophilaTemporalDiagnosisBoundary =
  drosophila-temporal-diagnosis-boundary true true true false false
