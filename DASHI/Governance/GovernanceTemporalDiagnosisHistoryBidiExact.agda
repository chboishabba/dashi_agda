module DASHI.Governance.GovernanceTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Governance.GovernanceDiagnosisRepairSchedulerBidiExact as Governance
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Progress
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection

------------------------------------------------------------------------
-- GOVERNANCE REPAIR WITH TEMPORAL DIAGNOSIS HISTORY
------------------------------------------------------------------------

reactivatedFrameDiagnosisStillRoutesToObserverRepair :
  Governance.repairRoute Outcome.frameConflict ≡ Progress.addNewCoordinate
reactivatedFrameDiagnosisStillRoutesToObserverRepair = refl

priorFrameEliminationStillAuditable :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorFrameEliminationStillAuditable =
  Temporal.priorEliminationStillPresentAfterReactivation

frameControlMayBecomeSalientAgain :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Projection.liveProjection Projection.afterReactivationBundle)
frameControlMayBecomeSalientAgain =
  Recalibration.frameCheckSalientAfterReactivation

authorityMismatchRemainsDistinctFromEpistemicRepair :
  Governance.repairRoute Outcome.authorityMismatch
  ≡ Progress.establishIndependentProvenance
authorityMismatchRemainsDistinctFromEpistemicRepair = refl

data ReactivatedGovernanceDiagnosisMeansPriorPolicyWasFalse : Set where
data DiagnosisHistoryCreatesMandateAuthority : Set where

reactivatedDiagnosisDoesNotRetroactivelyFalsifyPriorPolicy :
  ReactivatedGovernanceDiagnosisMeansPriorPolicyWasFalse → ⊥
reactivatedDiagnosisDoesNotRetroactivelyFalsifyPriorPolicy ()

diagnosisHistoryDoesNotCreateMandateAuthority :
  DiagnosisHistoryCreatesMandateAuthority → ⊥
diagnosisHistoryDoesNotCreateMandateAuthority ()

record GovernanceTemporalDiagnosisBoundary : Set where
  constructor governance-temporal-diagnosis-boundary
  field
    governanceDiagnosisMayReactivate : Bool
    earlierEliminationRemainsAuditable : Bool
    debugMoveMayBecomeSalientAgain : Bool
    reactivationRetroactivelyFalsifiesPriorPolicy : Bool
    diagnosisHistoryCreatesAuthority : Bool

canonicalGovernanceTemporalDiagnosisBoundary : GovernanceTemporalDiagnosisBoundary
canonicalGovernanceTemporalDiagnosisBoundary =
  governance-temporal-diagnosis-boundary true true true false false
