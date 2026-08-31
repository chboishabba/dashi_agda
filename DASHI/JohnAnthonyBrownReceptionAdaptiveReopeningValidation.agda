module DASHI.JohnAnthonyBrownReceptionAdaptiveReopeningValidation where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Ternary27AdmissibilityPathDynamicsExact as BasePath
import DASHI.Governance.ReceptionEvidenceSelectiveReopeningExact as Reception
import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

------------------------------------------------------------------------
-- Base-path admissibility dynamics.
------------------------------------------------------------------------

swapReallyUnavailableBefore :
  BasePath.Operator.OperatorAdmitted
    (BasePath.b0 BasePath.canonicalAdmissionPath)
    BasePath.Operator.swapXYOperator → ⊥
swapReallyUnavailableBefore = BasePath.swapUnavailableAtPath0

swapReallyAvailableAfterFirstStep :
  BasePath.Operator.OperatorAdmitted
    (BasePath.b1 BasePath.canonicalAdmissionPath)
    BasePath.Operator.swapXYOperator
swapReallyAvailableAfterFirstStep = BasePath.swapAvailableAtPath1

rotationReallyAvailableAtFinalStep :
  BasePath.Operator.OperatorAdmitted
    (BasePath.b2 BasePath.canonicalAdmissionPath)
    BasePath.Operator.rotateXYZOperator
rotationReallyAvailableAtFinalStep = BasePath.rotateAvailableAtPath2

------------------------------------------------------------------------
-- Reception graph reopening.
------------------------------------------------------------------------

edgeReclassificationReopensMeaning :
  Reception.Dependency.ReopeningObligation
    Reception.ReceptionDepends
    Reception.edgeClassificationArtifact
    Reception.semanticTransportArtifact
edgeReclassificationReopensMeaning = Reception.edgeChangeReopensSemantic

sourceChangeReopensPolicy :
  Reception.Dependency.ReopeningObligation
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
  Brown.Dependency.ReopeningObligation
    Brown.BrownDepends
    Brown.institutionalBetrayalMeasurementEvidence
    Brown.h3IncrementalBetrayalClaim
betrayalMeasureReopensH3OnlyThroughDeclaredDependency =
  Brown.betrayalMeasureChangeReopensH3

receptionHistoryReopensH2Interpretation :
  Brown.Dependency.ReopeningObligation
    Brown.BrownDepends
    Brown.conceptualReceptionEdge
    Brown.h2OutcomeVectorClaim
receptionHistoryReopensH2Interpretation =
  Brown.receptionChangeReopensH2Interpretation

wholePaperDoesNotAutoInvalidate : Brown.OneChangedSourceInvalidatesWholePaper → ⊥
wholePaperDoesNotAutoInvalidate = Brown.oneChangedSourceDoesNotInvalidateWholePaper

staleClaimDoesNotAutoRefute : Brown.StaleBrownClaimIsRefuted → ⊥
staleClaimDoesNotAutoRefute = Brown.staleBrownClaimIsReopenableNotRefuted
