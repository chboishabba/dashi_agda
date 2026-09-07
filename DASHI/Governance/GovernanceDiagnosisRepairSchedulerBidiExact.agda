module DASHI.Governance.GovernanceDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Governance.PluralEpistemicRepairMethodologyBidiExact as Governance
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Progress

------------------------------------------------------------------------
-- GOVERNANCE REPAIR <-> DIAGNOSIS-FIBRE SCHEDULING
--
-- A policy/intervention residual may be observational, model-relative,
-- consumer-relative, provenance-relative, or authority-relative.  Do not route
-- every adverse outcome to 'more intervention' or 'more data'.
------------------------------------------------------------------------

governanceDiagnosisFibre : Diagnosis.DiagnosisFibre
governanceDiagnosisFibre Outcome.observationConflict = ⊤
governanceDiagnosisFibre Outcome.modelConflict = ⊤
governanceDiagnosisFibre Outcome.consumerMismatch = ⊤
governanceDiagnosisFibre Outcome.provenanceConflict = ⊤
governanceDiagnosisFibre Outcome.authorityMismatch = ⊤
governanceDiagnosisFibre _ = ⊥

repairRoute : Outcome.OutcomeDiagnosis → Progress.EpistemicProgressRoute
repairRoute Outcome.observationConflict = Progress.addNewCoordinate
repairRoute Outcome.frameConflict = Progress.addNewCoordinate
repairRoute Outcome.premiseConflict = Progress.narrowLiveSet
repairRoute Outcome.ruleConflict = Progress.narrowLiveSet
repairRoute Outcome.modelConflict = Progress.narrowLiveSet
repairRoute Outcome.consumerMismatch = Progress.reformulateQuestion
repairRoute Outcome.provenanceConflict = Progress.establishIndependentProvenance
repairRoute Outcome.authorityMismatch = Progress.establishIndependentProvenance
repairRoute Outcome.insufficientResolution = Progress.addNewCoordinate

consumerMismatchRoutesToReformulation :
  repairRoute Outcome.consumerMismatch ≡ Progress.reformulateQuestion
consumerMismatchRoutesToReformulation = refl

provenanceConflictRoutesToIndependentProvenance :
  repairRoute Outcome.provenanceConflict ≡ Progress.establishIndependentProvenance
provenanceConflictRoutesToIndependentProvenance = refl

observerConflictRoutesToNewCoordinate :
  repairRoute Outcome.observationConflict ≡ Progress.addNewCoordinate
observerConflictRoutesToNewCoordinate = refl

existingGovernanceObserverRepairBoundary =
  Governance.deterministicRechartStillCannotRestoreCollapsedPair

data AdverseGovernanceOutcomeMeansMoreIntervention : Set where
data AuthorityMismatchSolvedByEpistemicEvidenceAlone : Set where

adverseOutcomeDoesNotMeanMoreIntervention :
  AdverseGovernanceOutcomeMeansMoreIntervention → ⊥
adverseOutcomeDoesNotMeanMoreIntervention ()

authorityMismatchNotSolvedByEvidenceAlone :
  AuthorityMismatchSolvedByEpistemicEvidenceAlone → ⊥
authorityMismatchNotSolvedByEvidenceAlone ()

record GovernanceDiagnosisSchedulerBoundary : Set where
  constructor governance-diagnosis-scheduler-boundary
  field
    governanceResidualMayHaveMultipleDiagnoses : Bool
    consumerMismatchMayCallForReformulation : Bool
    provenanceConflictMayCallForIndependentSource : Bool
    observerConflictMayCallForNewCoordinate : Bool
    adverseOutcomeAutomaticallyMeansMoreIntervention : Bool

canonicalGovernanceDiagnosisSchedulerBoundary : GovernanceDiagnosisSchedulerBoundary
canonicalGovernanceDiagnosisSchedulerBoundary =
  governance-diagnosis-scheduler-boundary true true true true false
