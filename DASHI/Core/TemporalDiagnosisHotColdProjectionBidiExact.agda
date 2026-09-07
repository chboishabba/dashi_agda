module DASHI.Core.TemporalDiagnosisHotColdProjectionBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Temporal
import DASHI.Cognition.PNF.HotColdExecutionProjection as HotCold

------------------------------------------------------------------------
-- DIAGNOSIS HISTORY = COLD AUTHORITY; CURRENT LIVE FIBRE = HOT PROJECTION
------------------------------------------------------------------------

DiagnosisHistory : Set₁
DiagnosisHistory = Temporal.DiagnosisHistoryBundle

CurrentDiagnosisFibre : Set₁
CurrentDiagnosisFibre = Diagnosis.DiagnosisFibre

rebuildCurrentDiagnosisFibre : DiagnosisHistory → CurrentDiagnosisFibre
rebuildCurrentDiagnosisFibre = Temporal.liveProjection

maintainedCurrentDiagnosisFibre : DiagnosisHistory → CurrentDiagnosisFibre
maintainedCurrentDiagnosisFibre = Temporal.liveProjection

diagnosisHotColdProjection :
  HotCold.HotColdProjection DiagnosisHistory CurrentDiagnosisFibre
diagnosisHotColdProjection =
  HotCold.hotColdProjection
    rebuildCurrentDiagnosisFibre
    maintainedCurrentDiagnosisFibre
    (λ history → refl)

maintainedDiagnosisEqualsRebuilt :
  (history : DiagnosisHistory) →
  HotCold.maintainedCurrent diagnosisHotColdProjection history
  ≡ HotCold.rebuildCurrent diagnosisHotColdProjection history
maintainedDiagnosisEqualsRebuilt history = refl

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
  HotCold.rebuildCurrent diagnosisHotColdProjection
    Temporal.beforeReactivationBundle
    (DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact.frameConflict)
  → ⊥
beforeHotFrameNotLive = Temporal.frameNotLiveBefore

afterHotFrameLive :
  HotCold.rebuildCurrent diagnosisHotColdProjection
    Temporal.afterReactivationBundle
    (DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact.frameConflict)
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

canonicalTemporalDiagnosisHotColdBoundary : TemporalDiagnosisHotColdBoundary
canonicalTemporalDiagnosisHotColdBoundary =
  temporal-diagnosis-hot-cold-boundary true true true true false
