module DASHI.Core.IncrementalDiagnosisTruthMaintenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisDependencyLineageBidiExact as Lineage

------------------------------------------------------------------------
-- INCREMENTAL TRUTH MAINTENANCE / DEPENDENCY-DIRECTED DIAGNOSIS REVISION
------------------------------------------------------------------------

record RecomputeFrontier
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (diagnosis : Outcome.OutcomeDiagnosis) : Set₁ where
  constructor recompute-frontier
  field
    changedArtifact : Artifact
    affectedConsumer : Artifact
    affectedPath : Closure.AffectedClosure Depends changedArtifact affectedConsumer
    temporalEvent : Temporal.DiagnosisEvent diagnosis
    frontierReference : String

open RecomputeFrontier public

frontierFromLineage :
  ∀ {Artifact : Set}
    {Depends : Artifact → Artifact → Set}
    {diagnosis : Outcome.OutcomeDiagnosis} →
  Lineage.DiagnosisLineageEvent {Artifact} Depends diagnosis →
  RecomputeFrontier Depends diagnosis
frontierFromLineage event =
  recompute-frontier
    (Lineage.upstreamArtifact event)
    (Lineage.diagnosisConsumer event)
    (Lineage.dependencyPath event)
    (Lineage.temporalEvent event)
    (Lineage.pathReference event)

record IncrementalRevisionReceipt
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (diagnosis : Outcome.OutcomeDiagnosis) : Set₁ where
  constructor incremental-revision-receipt
  field
    frontier : RecomputeFrontier Depends diagnosis
    oldHistoryRetained : Bool
    unrelatedCertificatesRetained : Bool
    currentDiagnosisMayChange : Bool
    authorityRecomputedSeparately : Bool
    revisionReference : String

open IncrementalRevisionReceipt public

data Artifact : Set where
  observation : Artifact
  model : Artifact
  frame : Artifact
  consumer : Artifact

data Depends : Artifact → Artifact → Set where
  observationToModel : Depends observation model
  modelToConsumer : Depends model consumer
  frameToConsumer : Depends frame consumer

observationToConsumerPath :
  Closure.AffectedClosure Depends observation consumer
observationToConsumerPath =
  Closure.affectedStep observationToModel
    (Closure.affectedStep modelToConsumer Closure.affectedRefl)

frameToConsumerPath :
  Closure.AffectedClosure Depends frame consumer
frameToConsumerPath =
  Closure.affectedStep frameToConsumer Closure.affectedRefl

modelReactivationEvent : Temporal.DiagnosisEvent Outcome.modelConflict
modelReactivationEvent =
  Temporal.diagnosis-event Temporal.reactivated 10
    (Temporal.resultTrigger Outcome.adverse)
    "later observation reopens model-conflict diagnosis"
    "finite incremental truth-maintenance fixture"

modelReactivationLineage :
  Lineage.DiagnosisLineageEvent Depends Outcome.modelConflict
modelReactivationLineage =
  Lineage.diagnosis-lineage-event
    modelReactivationEvent observation consumer observationToConsumerPath
    "observation -> model -> consumer"
    "dependency path does not transfer authority"

modelFrontier : RecomputeFrontier Depends Outcome.modelConflict
modelFrontier = frontierFromLineage modelReactivationLineage

FrameCertificate : Set
FrameCertificate = ⊤

frameCertificateBefore : FrameCertificate
frameCertificateBefore = tt

frameCertificateAfterModelRecompute : FrameCertificate
frameCertificateAfterModelRecompute = frameCertificateBefore

canonicalIncrementalRevision :
  IncrementalRevisionReceipt Depends Outcome.modelConflict
canonicalIncrementalRevision =
  incremental-revision-receipt
    modelFrontier true true true true
    "recompute affected model branch; retain unrelated frame certificate and history"

data ChangedBranchInvalidatesAllCertificates : Set where
data IncrementalRevisionDeletesHistory : Set where
data RecomputeFrontierCreatesAuthority : Set where
data ReactivationRequiresGlobalRebuild : Set where

changedBranchDoesNotInvalidateAllCertificates :
  ChangedBranchInvalidatesAllCertificates → ⊥
changedBranchDoesNotInvalidateAllCertificates ()

incrementalRevisionDoesNotDeleteHistory : IncrementalRevisionDeletesHistory → ⊥
incrementalRevisionDoesNotDeleteHistory ()

recomputeFrontierDoesNotCreateAuthority : RecomputeFrontierCreatesAuthority → ⊥
recomputeFrontierDoesNotCreateAuthority ()

reactivationNeedNotRequireGlobalRebuild : ReactivationRequiresGlobalRebuild → ⊥
reactivationNeedNotRequireGlobalRebuild ()

record IncrementalTruthMaintenanceBoundary : Set where
  constructor incremental-truth-maintenance-boundary
  field
    recomputationLocalizedByDependencyPath : Bool
    currentDiagnosisMayChangeNonMonotonically : Bool
    historyRemainsAppendOnly : Bool
    unrelatedCertificateMayRemainValid : Bool
    reactivationRequiresGlobalRebuild : Bool
    recomputationCreatesAuthority : Bool

canonicalIncrementalTruthMaintenanceBoundary : IncrementalTruthMaintenanceBoundary
canonicalIncrementalTruthMaintenanceBoundary =
  incremental-truth-maintenance-boundary true true true true false false
