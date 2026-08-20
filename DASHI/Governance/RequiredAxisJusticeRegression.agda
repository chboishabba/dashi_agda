module DASHI.Governance.RequiredAxisJusticeRegression where

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Provenance
import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Governance.JusticeEvidenceQualifiedValidationExact as Qualified
import DASHI.Governance.JusticeProvenanceOutcomeLensExact as Lens
import DASHI.Governance.JusticeQueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Governance.JusticeRequiredAxisEvidenceExact as Evidence
import DASHI.Governance.MandateBackedAuthorityRoutingExact as MandateRouting
import DASHI.Governance.RequiredAxisAuthorityRoutingExact as EvidenceRouting
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing
import DASHI.Governance.TransitionResidual as Transition

------------------------------------------------------------------------
-- Focused regression for the support-square / required-axis cross-pollination.
------------------------------------------------------------------------

conflictAndMissingRemainDistinct :
  Support.supportState (Support.supportSquare true true)
  ≡ Support.supportState (Support.supportSquare false false) →
  ⊥
conflictAndMissingRemainDistinct = Support.conflictingIsNotMissing

pooledPositiveDoesNotResolveMissingRequiredAxis :
  Support.RequiredAxesResolved Support.demoFamily → ⊥
pooledPositiveDoesNotResolveMissingRequiredAxis =
  Support.demoPooledPositiveStillCannotResolveRequiredAxes

governancePresentationCannotRecoverEvidenceState :
  Qualified.GovernanceValidationDeterminesEvidenceState → ⊥
governancePresentationCannotRecoverEvidenceState =
  Qualified.governanceValidationCannotReconstructEvidenceState

missingEvidenceCannotBecomeViolationEvidence :
  Evidence.ResolvedViolation
    Evidence.demoJusticeGrid
    Transition.rightsInvariant
    Evidence.authorityMandateAxis →
  ⊥
missingEvidenceCannotBecomeViolationEvidence =
  Evidence.missingEvidenceCannotManufactureViolationDerivation
    Evidence.demoRightsMandateEvidenceMissing

rightsViolationEvidenceCannotFillMandateEvidence :
  Evidence.ResolvedSatisfaction
    Evidence.demoJusticeGrid
    Transition.rightsInvariant
    Evidence.authorityMandateAxis →
  ⊥
rightsViolationEvidenceCannotFillMandateEvidence =
  Evidence.rightsViolationEvidenceDoesNotFillMissingMandateEvidence

formerSupporterEvidenceCannotResolveCurrentAuthority :
  Support.RequiredAxesResolved
    (Evidence.routeEvidenceFamily Evidence.formerSupporterEvidenceProfile) →
  ⊥
formerSupporterEvidenceCannotResolveCurrentAuthority =
  Evidence.pooledRoutingEvidenceCannotManufactureCurrentAuthority

allRequiredEvidenceCanConstructAdmissibleRoute :
  Routing.AdmissibleRoute
    MandateRouting.demoRouting
    MandateRouting.delegatedResponseSituation
    MandateRouting.delegatedResponderRoute
allRequiredEvidenceCanConstructAdmissibleRoute =
  EvidenceRouting.canonicalEvidenceDerivedAdmissibleRoute

sameProjectionCanBeSurfaceAdequateAndRoutingInadequate :
  Adequacy.SameProjectionDifferentJusticeQueryAdequacy
sameProjectionCanBeSurfaceAdequateAndRoutingInadequate =
  Adequacy.sameIncidentProjectionAdequateForSurfaceNotRouting

publicOutcomeCannotReconstructJusticeProvenance :
  Lens.ExactSurfaceReconstruction → ⊥
publicOutcomeCannotReconstructJusticeProvenance =
  Lens.publicOutcomeCannotReconstructFullJusticeState

receiptReopensJusticeProvenance :
  (record : Lens.FineJusticeRecord) →
  Provenance.reopen
    Lens.justiceProvenanceBearingQuotient
    (Fibre.project Lens.justiceFibreCore record)
    (Provenance.receipt Lens.justiceProvenanceBearingQuotient record)
  ≡ record
receiptReopensJusticeProvenance =
  Lens.proofRelevantReceiptReopensFineJusticeState
