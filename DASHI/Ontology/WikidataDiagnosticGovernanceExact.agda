module DASHI.Ontology.WikidataDiagnosticGovernanceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.EpistemicInquiryGovernance as Governance

------------------------------------------------------------------------
-- Coordinate-wise governance of ontology diagnostics.
--
-- Cross-domain calibration:
-- Alice Brown & Megan Kimber (2026), DOI 10.1177/14697874261426374,
-- motivates the distinction between supplying evidence and constitutive
-- authority over questions, projections/coding frames, residuals and revision.
-- The concrete ontology-governance typing below is DASHI-local.
------------------------------------------------------------------------

data DiagnosticAgent : Set where
  sourceOntologyMaintainer : DiagnosticAgent
  targetOntologyCommunity : DiagnosticAgent
  formalChecker : DiagnosticAgent
  diagnosticAnalyst : DiagnosticAgent

data DiagnosticAuthorises : DiagnosticAgent → Governance.InquiryCoordinate → Set where
  sourceMaintainerShapesCarrier :
    DiagnosticAuthorises sourceOntologyMaintainer Governance.carrierCoordinate
  sourceMaintainerShapesQuestion :
    DiagnosticAuthorises sourceOntologyMaintainer Governance.questionCoordinate
  targetCommunityShapesProjection :
    DiagnosticAuthorises targetOntologyCommunity Governance.projectionCoordinate
  targetCommunityShapesResidualPolicy :
    DiagnosticAuthorises targetOntologyCommunity Governance.residualCoordinate
  targetCommunityShapesRevision :
    DiagnosticAuthorises targetOntologyCommunity Governance.revisionCoordinate
  targetCommunityShapesConsumerFamily :
    DiagnosticAuthorises targetOntologyCommunity Governance.consumerCoordinate

wikidataDiagnosticGovernance : Governance.EpistemicGovernance DiagnosticAgent
wikidataDiagnosticGovernance = Governance.epistemicGovernance DiagnosticAuthorises

formalCheckerHasNoAutomaticConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  DiagnosticAuthorises formalChecker coordinate → ⊥
formalCheckerHasNoAutomaticConstitutiveAuthority coordinate ()

diagnosticAnalystHasNoAutomaticConstitutiveAuthority :
  (coordinate : Governance.InquiryCoordinate) →
  DiagnosticAuthorises diagnosticAnalyst coordinate → ⊥
diagnosticAnalystHasNoAutomaticConstitutiveAuthority coordinate ()

formalCheckerCannotSelfAuthoriseRevision :
  DiagnosticAuthorises formalChecker Governance.revisionCoordinate → ⊥
formalCheckerCannotSelfAuthoriseRevision ()

diagnosticAnalystCannotSelfAuthoriseRevision :
  DiagnosticAuthorises diagnosticAnalyst Governance.revisionCoordinate → ⊥
diagnosticAnalystCannotSelfAuthoriseRevision ()

record DiagnosticFinding : Set where
  constructor diagnosticFinding

record RepairRecommendation : Set where
  constructor repairRecommendation

record EditMandate : Set where
  constructor editMandate

data FindingImpliesEditMandatePermission : Set where

diagnosticDetectionDoesNotConferEditAuthority :
  DiagnosticFinding → FindingImpliesEditMandatePermission → EditMandate
diagnosticDetectionDoesNotConferEditAuthority finding ()

record DiagnosticGovernanceBoundary : Set where
  constructor diagnosticGovernanceBoundary
  field
    evidenceContributionEqualsConstitutiveAuthority : Bool
    findingEqualsEditMandate : Bool
    targetRevisionRequiresIndependentGovernance : Bool

canonicalDiagnosticGovernanceBoundary : DiagnosticGovernanceBoundary
canonicalDiagnosticGovernanceBoundary =
  diagnosticGovernanceBoundary false false true
