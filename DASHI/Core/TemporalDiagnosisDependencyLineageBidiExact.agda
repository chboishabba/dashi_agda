module DASHI.Core.TemporalDiagnosisDependencyLineageBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal

record DiagnosisLineageEvent
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (diagnosis : Outcome.OutcomeDiagnosis) : Set₁ where
  constructor diagnosis-lineage-event
  field
    temporalEvent : Temporal.DiagnosisEvent diagnosis
    upstreamArtifact : Artifact
    diagnosisConsumer : Artifact
    dependencyPath : Closure.AffectedClosure Depends upstreamArtifact diagnosisConsumer
    pathReference : String
    sourceAuthorityReference : String

open DiagnosisLineageEvent public

record LocalizedReactivation
    {Artifact : Set}
    (Depends : Artifact → Artifact → Set)
    (diagnosis : Outcome.OutcomeDiagnosis) : Set₁ where
  constructor localized-reactivation
  field
    priorElimination : DiagnosisLineageEvent Depends diagnosis
    laterReactivation : DiagnosisLineageEvent Depends diagnosis
    priorWasElimination :
      Temporal.transition (temporalEvent priorElimination) ≡ Temporal.eliminated
    laterWasReactivation :
      Temporal.transition (temporalEvent laterReactivation) ≡ Temporal.reactivated
    sameConsumer :
      diagnosisConsumer priorElimination ≡ diagnosisConsumer laterReactivation
    changedUpstream : Artifact
    changedPath :
      Closure.AffectedClosure Depends changedUpstream
        (diagnosisConsumer laterReactivation)
    reactivationReference : String

open LocalizedReactivation public

data ReactivationInvalidatesWholeGraph : Set where
data DependencyPathTransfersAuthority : Set where
data LaterPathDeletesEarlierPath : Set where
data SameDiagnosisMeansSameUpstreamCause : Set where

reactivationDoesNotInvalidateWholeGraph : ReactivationInvalidatesWholeGraph → ⊥
reactivationDoesNotInvalidateWholeGraph ()

dependencyPathDoesNotTransferAuthority : DependencyPathTransfersAuthority → ⊥
dependencyPathDoesNotTransferAuthority ()

laterPathDoesNotDeleteEarlierPath : LaterPathDeletesEarlierPath → ⊥
laterPathDoesNotDeleteEarlierPath ()

sameDiagnosisNeedNotMeanSameUpstreamCause : SameDiagnosisMeansSameUpstreamCause → ⊥
sameDiagnosisNeedNotMeanSameUpstreamCause ()

record TemporalDiagnosisDependencyLineageBoundary : Set where
  constructor temporal-diagnosis-dependency-lineage-boundary
  field
    eventCarriesExactDependencyPath : Bool
    localizedReactivationChecksTransitions : Bool
    reactivationMayLocalizeToChangedSubgraph : Bool
    sameDiagnosisMayHaveDifferentHistoricalCauses : Bool
    lineageTransfersAuthority : Bool
    reactivationErasesEarlierLineage : Bool
    reactivationInvalidatesWholeGraph : Bool

canonicalTemporalDiagnosisDependencyLineageBoundary :
  TemporalDiagnosisDependencyLineageBoundary
canonicalTemporalDiagnosisDependencyLineageBoundary =
  temporal-diagnosis-dependency-lineage-boundary true true true true false false false
