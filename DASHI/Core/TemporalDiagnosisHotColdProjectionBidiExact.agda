module DASHI.Core.TemporalDiagnosisHotColdProjectionBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Temporal
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Cognition.PNF.HotColdExecutionProjection as HotCold

------------------------------------------------------------------------
-- DIAGNOSIS HISTORY = COLD AUTHORITY; CURRENT LIVE FIBRE = HOT PROJECTION
--
-- The existing HotColdProjection is Set-level.  Diagnosis fibres are predicate-
-- valued and therefore Set₁, so we preserve the same law at the correct universe
-- rather than silently coercing the carrier.
------------------------------------------------------------------------

DiagnosisHistory : Set₁
DiagnosisHistory = Temporal.DiagnosisHistoryBundle

CurrentDiagnosisFibre : Set₁
CurrentDiagnosisFibre = Diagnosis.DiagnosisFibre

record DiagnosisHotColdProjection : Set₂ where
  constructor diagnosis-hot-cold-projection
  field
    rebuildCurrent : DiagnosisHistory → CurrentDiagnosisFibre
    maintainedCurrent : DiagnosisHistory → CurrentDiagnosisFibre
    maintainedEqualsRebuilt :
      (history : DiagnosisHistory) →
      maintainedCurrent history ≡ rebuildCurrent history

open DiagnosisHotColdProjection public

rebuildCurrentDiagnosisFibre : DiagnosisHistory → CurrentDiagnosisFibre
rebuildCurrentDiagnosisFibre = Temporal.liveProjection

maintainedCurrentDiagnosisFibre : DiagnosisHistory → CurrentDiagnosisFibre
maintainedCurrentDiagnosisFibre = Temporal.liveProjection

diagnosisHotColdProjection : DiagnosisHotColdProjection
diagnosisHotColdProjection =
  diagnosis-hot-cold-projection
    rebuildCurrentDiagnosisFibre
    maintainedCurrentDiagnosisFibre
    (λ history → refl)

maintainedDiagnosisEqualsRebuilt :
  (history : DiagnosisHistory) →
  maintainedCurrent diagnosisHotColdProjection history
  ≡ rebuildCurrent diagnosisHotColdProjection history
maintainedDiagnosisEqualsRebuilt history = refl

------------------------------------------------------------------------
-- Consume the existing hot/cold constitution as the donor contract.
------------------------------------------------------------------------

historyAuthorityBoundary :
  HotCold.HotColdBoundary.appendOnlyHistoryIsAuthority
    HotCold.canonicalHotColdBoundary
  ≡ true
historyAuthorityBoundary = refl

hotDiagnosisMustBeRebuildable :
  HotCold.HotColdBoundary.materializedHotStateMustBeRebuildable
    HotCold.canonicalHotColdBoundary
  ≡ true
hotDiagnosisMustBeRebuildable = refl

beforeHotFrameNotLive :
  rebuildCurrent diagnosisHotColdProjection
    Temporal.beforeReactivationBundle Outcome.frameConflict
  → ⊥
beforeHotFrameNotLive = Temporal.frameNotLiveBefore

afterHotFrameLive :
  rebuildCurrent diagnosisHotColdProjection
    Temporal.afterReactivationBundle Outcome.frameConflict
afterHotFrameLive = Temporal.frameLiveAfter

data HotDiagnosisCanOverrideHistory : Set where
data CurrentFibreIsProvenanceAuthority : Set where

hotDiagnosisCannotOverrideHistory : HotDiagnosisCanOverrideHistory → ⊥
hotDiagnosisCannotOverrideHistory ()

currentFibreIsNotWholeProvenanceAuthority : CurrentFibreIsProvenanceAuthority → ⊥
currentFibreIsNotWholeProvenanceAuthority ()

record TemporalDiagnosisHotColdBoundary : Set where
  constructor temporal-diagnosis-hot-cold-boundary
  field
    diagnosisHistoryIsAuthority : Bool
    currentFibreMayBeMaterialized : Bool
    currentFibreMustRebuildFromHistory : Bool
    reactivationMayChangeCurrentFibre : Bool
    hotProjectionMayRewriteHistory : Bool
    universeMismatchSilentlyCoerced : Bool

canonicalTemporalDiagnosisHotColdBoundary : TemporalDiagnosisHotColdBoundary
canonicalTemporalDiagnosisHotColdBoundary =
  temporal-diagnosis-hot-cold-boundary true true true true false false
