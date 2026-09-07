module DASHI.JohnAnthonyBrownReceptionAdaptiveReopeningValidation where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.TemporalDiagnosisDependencyLineageBidiExact as Lineage
import DASHI.Foundations.Base369Ternary27AdmissibilityPathDynamicsExact as BasePath
import DASHI.Foundations.Base369Ternary27StabiliserOperatorHolonomyExact as Operator
import DASHI.Governance.ReceptionEvidenceSelectiveReopeningExact as Reception
import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest
import DASHI.Culture.JohnAnthonyBrownDiagnosisRepairSchedulerBidiExact as Diagnosis
import DASHI.Culture.JohnAnthonyBrownTemporalDiagnosisDependencyLineageBidiExact as TemporalLineage

------------------------------------------------------------------------
-- Base-path admissibility dynamics.
------------------------------------------------------------------------

swapReallyUnavailableBefore :
  Operator.OperatorAdmitted
    (BasePath.b0 BasePath.canonicalAdmissionPath)
    Operator.swapXYOperator → ⊥
swapReallyUnavailableBefore = BasePath.swapUnavailableAtPath0

swapReallyAvailableAfterFirstStep :
  Operator.OperatorAdmitted
    (BasePath.b1 BasePath.canonicalAdmissionPath)
    Operator.swapXYOperator
swapReallyAvailableAfterFirstStep = BasePath.swapAvailableAtPath1

rotationReallyAvailableAtFinalStep :
  Operator.OperatorAdmitted
    (BasePath.b2 BasePath.canonicalAdmissionPath)
    Operator.rotateXYZOperator
rotationReallyAvailableAtFinalStep = BasePath.rotateAvailableAtPath2

------------------------------------------------------------------------
-- Reception graph reopening.
------------------------------------------------------------------------

edgeReclassificationReopensMeaning :
  Dependency.ReopeningObligation
    Reception.ReceptionDepends
    Reception.edgeClassificationArtifact
    Reception.semanticTransportArtifact
edgeReclassificationReopensMeaning = Reception.edgeChangeReopensSemantic

sourceChangeReopensPolicy :
  Dependency.ReopeningObligation
    Reception.ReceptionDepends
    Reception.sourceReceiptArtifact
    Reception.downstreamPolicyArtifact
sourceChangeReopensPolicy = Reception.sourceChangeReopensPolicyTransitively

------------------------------------------------------------------------
-- John Anthony Brown H1-H5 selective reopening.
------------------------------------------------------------------------

johnBrownAuthorPinned : Brown.paperAuthor ≡ "John Anthony Brown"
johnBrownAuthorPinned = refl

h1Pinned : Manifest.key Manifest.h1Manifest ≡ Manifest.H1
h1Pinned = Brown.h1StillH1

h5Pinned : Manifest.key Manifest.h5Manifest ≡ Manifest.H5
h5Pinned = Brown.h5StillH5

betrayalMeasureReopensH3OnlyThroughDeclaredDependency :
  Dependency.ReopeningObligation
    Brown.BrownDepends
    Brown.institutionalBetrayalMeasurementEvidence
    Brown.h3IncrementalBetrayalClaim
betrayalMeasureReopensH3OnlyThroughDeclaredDependency =
  Brown.betrayalMeasureChangeReopensH3

receptionHistoryReopensH2Interpretation :
  Dependency.ReopeningObligation
    Brown.BrownDepends
    Brown.conceptualReceptionEdge
    Brown.h2OutcomeVectorClaim
receptionHistoryReopensH2Interpretation =
  Brown.receptionChangeReopensH2Interpretation

wholePaperDoesNotAutoInvalidate : Brown.OneChangedSourceInvalidatesWholePaper → ⊥
wholePaperDoesNotAutoInvalidate = Brown.oneChangedSourceDoesNotInvalidateWholePaper

staleClaimDoesNotAutoRefute : Brown.StaleBrownClaimIsRefuted → ⊥
staleClaimDoesNotAutoRefute = Brown.staleBrownClaimIsReopenableNotRefuted

------------------------------------------------------------------------
-- Diagnosis scheduler + temporal dependency-lineage return.
------------------------------------------------------------------------

receptionFrameRequestsRechart :
  Diagnosis.brownRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
receptionFrameRequestsRechart = Diagnosis.receptionFrameConflictRequestsRechart

receptionReactivationLocalizedToH2 :
  Lineage.LocalizedReactivation Brown.BrownDepends Outcome.frameConflict
receptionReactivationLocalizedToH2 = TemporalLineage.localizedReceptionReactivation

h1ObservationReactivationMayUseDifferentUpstreamMeasurement :
  Lineage.LocalizedReactivation Brown.BrownDepends Outcome.observationConflict
h1ObservationReactivationMayUseDifferentUpstreamMeasurement =
  TemporalLineage.localizedH1ObservationReactivation
