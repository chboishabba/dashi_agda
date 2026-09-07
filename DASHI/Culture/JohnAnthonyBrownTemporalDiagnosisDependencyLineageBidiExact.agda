module DASHI.Culture.JohnAnthonyBrownTemporalDiagnosisDependencyLineageBidiExact where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisExperimentPortfolioBidiExact as Portfolio
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisDependencyLineageBidiExact as Lineage

receptionToH2Path :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.conceptualReceptionEdge Brown.h2OutcomeVectorClaim
receptionToH2Path =
  Closure.affectedStep Brown.receptionToAutonomyDefinition
    (Closure.affectedStep Brown.autonomyDefinitionToH2 Closure.affectedRefl)

exposureToH1Path :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.exposureMeasurementEvidence Brown.h1AssociationClaim
exposureToH1Path = Closure.affectedStep Brown.exposureToH1 Closure.affectedRefl

outcomeToH1Path :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.outcomeMeasurementEvidence Brown.h1AssociationClaim
outcomeToH1Path = Closure.affectedStep Brown.outcomeToH1 Closure.affectedRefl

confoundingToH5Path :
  Closure.AffectedClosure
    Brown.BrownDepends Brown.confoundingModelEvidence Brown.h5AdjustedAssociationClaim
confoundingToH5Path = Closure.affectedStep Brown.confoundingToH5 Closure.affectedRefl

receptionFrameActivated : Temporal.DiagnosisEvent Outcome.frameConflict
receptionFrameActivated =
  Temporal.diagnosis-event Temporal.activated 1
    (Temporal.resultTrigger Outcome.indeterminate)
    "reception/concept-definition audit leaves framing diagnosis live for H2 interpretation"
    "paper-audit event; not a claim that the paper's H2 is false"

receptionFrameEliminated : Temporal.DiagnosisEvent Outcome.frameConflict
receptionFrameEliminated =
  Temporal.diagnosis-event Temporal.eliminated 2
    (Temporal.debugMoveTrigger Portfolio.frameControl)
    "concept/reception audit resolves the then-current framing issue"
    "historical elimination remains auditable"

receptionFrameReactivated : Temporal.DiagnosisEvent Outcome.frameConflict
receptionFrameReactivated =
  Temporal.diagnosis-event Temporal.reactivated 3
    (Temporal.resultTrigger Outcome.indeterminate)
    "later reception evidence makes H2 framing review relevant again"
    "reactivation appends; it does not rewrite the prior audit"

receptionActivationLineage :
  Lineage.DiagnosisLineageEvent Brown.BrownDepends Outcome.frameConflict
receptionActivationLineage =
  Lineage.diagnosis-lineage-event
    receptionFrameActivated Brown.conceptualReceptionEdge Brown.h2OutcomeVectorClaim
    receptionToH2Path
    "conceptual reception -> autonomy definition -> H2 outcome-vector claim"
    "external reception sources and John Brown paper authorship remain distinct"

receptionEliminationLineage :
  Lineage.DiagnosisLineageEvent Brown.BrownDepends Outcome.frameConflict
receptionEliminationLineage =
  Lineage.diagnosis-lineage-event
    receptionFrameEliminated Brown.conceptualReceptionEdge Brown.h2OutcomeVectorClaim
    receptionToH2Path
    "same declared H2 audit path at elimination time"
    "no authorship or authority transfer through dependency edges"

receptionReactivationLineage :
  Lineage.DiagnosisLineageEvent Brown.BrownDepends Outcome.frameConflict
receptionReactivationLineage =
  Lineage.diagnosis-lineage-event
    receptionFrameReactivated Brown.conceptualReceptionEdge Brown.h2OutcomeVectorClaim
    receptionToH2Path
    "same H2 consumer reopened by later reception-history change"
    "stale wording is reopenable, not automatically refuted"

localizedReceptionReactivation :
  Lineage.LocalizedReactivation Brown.BrownDepends Outcome.frameConflict
localizedReceptionReactivation =
  Lineage.localized-reactivation
    receptionEliminationLineage
    receptionReactivationLineage
    refl
    refl
    refl
    Brown.conceptualReceptionEdge
    receptionToH2Path
    "localize reactivation to the reception -> autonomy-definition -> H2 subgraph"

exposureObservationEliminated : Temporal.DiagnosisEvent Outcome.observationConflict
exposureObservationEliminated =
  Temporal.diagnosis-event Temporal.eliminated 4
    (Temporal.debugMoveTrigger Portfolio.repeatObservation)
    "exposure-measurement observation issue eliminated for the then-current H1 audit"
    "synthetic audit chronology over declared BrownDepends edges"

outcomeObservationReactivated : Temporal.DiagnosisEvent Outcome.observationConflict
outcomeObservationReactivated =
  Temporal.diagnosis-event Temporal.reactivated 5
    (Temporal.resultTrigger Outcome.adverse)
    "later outcome-measurement evidence reactivates an observation diagnosis for H1"
    "same diagnosis label does not imply same upstream source"

exposureObservationLineage :
  Lineage.DiagnosisLineageEvent Brown.BrownDepends Outcome.observationConflict
exposureObservationLineage =
  Lineage.diagnosis-lineage-event
    exposureObservationEliminated Brown.exposureMeasurementEvidence Brown.h1AssociationClaim
    exposureToH1Path
    "exposure measurement -> H1 association claim"
    "measurement evidence remains source-local"

outcomeObservationLineage :
  Lineage.DiagnosisLineageEvent Brown.BrownDepends Outcome.observationConflict
outcomeObservationLineage =
  Lineage.diagnosis-lineage-event
    outcomeObservationReactivated Brown.outcomeMeasurementEvidence Brown.h1AssociationClaim
    outcomeToH1Path
    "outcome measurement -> H1 association claim"
    "later H1 reactivation does not retroactively invalidate exposure evidence"

localizedH1ObservationReactivation :
  Lineage.LocalizedReactivation Brown.BrownDepends Outcome.observationConflict
localizedH1ObservationReactivation =
  Lineage.localized-reactivation
    exposureObservationLineage
    outcomeObservationLineage
    refl
    refl
    refl
    Brown.outcomeMeasurementEvidence
    outcomeToH1Path
    "same H1 observation diagnosis reactivated through a different upstream measurement edge"

selectiveReopeningBoundaryRetained : Brown.JohnBrownSelectiveReopeningBoundary
selectiveReopeningBoundaryRetained = Brown.canonicalJohnBrownSelectiveReopeningBoundary

data ReactivationInvalidatesWholePaper : Set where
data SameDiagnosisMeansSameMeasurementSource : Set where
data DependencyLineageTransfersAuthorship : Set where

reactivationDoesNotInvalidateWholePaper : ReactivationInvalidatesWholePaper → ⊥
reactivationDoesNotInvalidateWholePaper ()

sameDiagnosisNeedNotMeanSameMeasurementSource :
  SameDiagnosisMeansSameMeasurementSource → ⊥
sameDiagnosisNeedNotMeanSameMeasurementSource ()

dependencyLineageDoesNotTransferAuthorship : DependencyLineageTransfersAuthorship → ⊥
dependencyLineageDoesNotTransferAuthorship ()

record JohnBrownTemporalDiagnosisLineageBoundary : Set where
  constructor john-brown-temporal-diagnosis-lineage-boundary
  field
    H1ToH5RemainDistinctConsumers : Bool
    temporalEventCarriesExactBrownDependencyPath : Bool
    reactivationMayLocalizeToH2ReceptionSubgraph : Bool
    sameDiagnosisMayUseDifferentH1MeasurementPaths : Bool
    reactivationInvalidatesWholePaper : Bool
    dependencyPathTransfersAuthorship : Bool
    staleClaimEqualsRefutation : Bool

canonicalJohnBrownTemporalDiagnosisLineageBoundary :
  JohnBrownTemporalDiagnosisLineageBoundary
canonicalJohnBrownTemporalDiagnosisLineageBoundary =
  john-brown-temporal-diagnosis-lineage-boundary true true true true false false false
