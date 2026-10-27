{-# OPTIONS --safe #-}
module DASHI.Unified.GovernedLegalWorkflowComplianceTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Workflow
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Ibrahim
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.LegalDecisionDoubleProjectionExact as LegalDecision
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

------------------------------------------------------------------------
-- GOVERNED LEGAL WORKFLOW / COMPLIANCE TOE EXTENSION
--
-- Reuse the current-master governed legal workflow owner from PR #1331.
-- Add only compliance firewalls not already exported by that owner.
-- Keep the Fleet/Ibrahim receipt separate and canonical.
-- Keep Actionstep-style vendor identity outside theorem authority.
------------------------------------------------------------------------

QualificationAutomaticallyForensicCompliance : Set
QualificationAutomaticallyForensicCompliance =
  Expert.QualificationAutomaticallyForensicCompliance

LegalReviewDecisionCreatesClaimTruth : Set
LegalReviewDecisionCreatesClaimTruth =
  Review.LegalReviewDecisionCreatesClaimTruth

OfficialLegalSurfaceRecoversFineState : Set
OfficialLegalSurfaceRecoversFineState =
  NF.FactorsThrough LegalDecision.officialSurface LegalDecision.fineLegalStateOf

LegalOnlyCreatesLegitimacy : Set₁
LegalOnlyCreatesLegitimacy =
  Legitimacy.AdmittedLegitimacy Legitimacy.demoEvidence Legitimacy.legalOnly

expertQualificationDoesNotCreateForensicCompliance :
  QualificationAutomaticallyForensicCompliance → ⊥
expertQualificationDoesNotCreateForensicCompliance =
  Expert.qualificationDoesNotAutomaticallyProveForensicCompliance

reportAdmissionDoesNotRepairMissingInput :
  Expert.ReportAdmissionRepairsMissingInput → ⊥
reportAdmissionDoesNotRepairMissingInput =
  Expert.reportAdmissionDoesNotRepairMissingInput

legalReviewDoesNotCreateClaimTruth :
  LegalReviewDecisionCreatesClaimTruth → ⊥
legalReviewDoesNotCreateClaimTruth =
  Review.legalReviewDecisionDoesNotCreateClaimTruth

officialLegalSurfaceDoesNotRecoverFineState :
  OfficialLegalSurfaceRecoversFineState → ⊥
officialLegalSurfaceDoesNotRecoverFineState =
  LegalDecision.officialSurfaceCannotRecoverFineLegalState

officialActionDoesNotRecoverAutonomyAndAuthority :
  NF.FactorsThrough
    LegalDecision.autonomyOfficialSurface
    LegalDecision.fineAutonomyLegalStateOf
  → ⊥
officialActionDoesNotRecoverAutonomyAndAuthority =
  LegalDecision.officialActionCannotRecoverAutonomyAndAuthority

legalityAloneDoesNotCreateLegitimacy :
  LegalOnlyCreatesLegitimacy → ⊥
legalityAloneDoesNotCreateLegitimacy =
  Legitimacy.legalOnlyIsNotAdmittedLegitimacy

missingAdmissibilityStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
  ≡ Governed.abstain
missingAdmissibilityStillAbstains =
  Promotion.missingAdmissibilityAbstains

missingValidationStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
  ≡ Governed.abstain
missingValidationStillAbstains =
  Promotion.missingValidationAbstains

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F frame.
--
-- Reuse the shared TOE process receipt. This frame records process constraints.
-- It does not create legal, physical, historical, or Monster authority.
------------------------------------------------------------------------

canonicalGovernedLegalWorkflowComplianceZKPFrame : Ibrahim.TOEZKPFrame
canonicalGovernedLegalWorkflowComplianceZKPFrame =
  Ibrahim.toe-zkp-frame
    "converge SensibLaw and Actionstep-style governance invariants into the existing DASHI TOE roots"
    "reuse canonical legal, promotion, Fleet, and Ibrahim theorem owners before any extension"
    "coalesce exact non-promotion firewalls into the existing governed legal workflow compliance owner"
    "workflow state, vendor identity, review state, exact reuse, spectral priority, and external counts do not create truth or authority"
    "one disjoint legal-governance normalization lane; physics, Fleet, and Ibrahim owners remain separate"
    "canonical owners exist; the 584 discharged fibres remain discharged; only the 58 formal gaps remain targetable; ESD surfaces are read-only"
    "ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma, and C4/PlantUML are process lenses only"
    "TOE root, Unified facade, and Unifier expose the same legal firewalls and Fleet/Ibrahim boundaries"
    "kernel check, exact-owner read-back, trust-escape audit, ESD diff audit, and lineage/referee checks"
    false false false false

------------------------------------------------------------------------
-- One receipt. The existing owners retain theorem authority.
------------------------------------------------------------------------

record GovernedLegalWorkflowComplianceTOEReceipt : Set₁ where
  field
    workflowHandoff :
      Workflow.GovernedLegalWorkflowTOEInvariantHandoff
    workflowHandoffIsCanonical :
      workflowHandoff
      ≡ Workflow.canonicalGovernedLegalWorkflowTOEInvariantHandoff

    expertQualificationFirewall :
      QualificationAutomaticallyForensicCompliance → ⊥
    reportAdmissionMissingInputFirewall :
      Expert.ReportAdmissionRepairsMissingInput → ⊥
    legalReviewTruthFirewall :
      LegalReviewDecisionCreatesClaimTruth → ⊥
    officialSurfaceFineStateFirewall :
      OfficialLegalSurfaceRecoversFineState → ⊥
    legalityLegitimacyFirewall :
      LegalOnlyCreatesLegitimacy → ⊥

    actionstepStyleVendorIdentityCreatesAuthority : Bool
    actionstepStyleVendorIdentityCreatesAuthorityIsFalse :
      actionstepStyleVendorIdentityCreatesAuthority ≡ false
    actionstepStyleTargetNeedsOwnAuthorityWitness : Bool
    actionstepStyleTargetNeedsOwnAuthorityWitnessIsTrue :
      actionstepStyleTargetNeedsOwnAuthorityWitness ≡ true

    ibrahimRecognitionBoundary :
      Ibrahim.RecognitionRouteParetoBoundary
    ibrahimSearchPriorityFirewall :
      Ibrahim.SearchPriorityCreatesProof → ⊥

    fleetFormalGapCount : Nat
    fleetFormalGapCountIs58 : fleetFormalGapCount ≡ 58
    fleetDischargedCount : Nat
    fleetDischargedCountIs584 : fleetDischargedCount ≡ 584
    fleetContradictionCount : Nat
    fleetContradictionCountIs44 : fleetContradictionCount ≡ 44

    fleetPriorityFirewall :
      Fleet.FleetEigenPriorityCreatesProof → ⊥
    fleetCountDischargeFirewall :
      Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
    fleetDischargedRetargetFirewall :
      Fleet.FleetDischargedFibreRetargetPermission → ⊥
    fleetContradictionRelabelFirewall :
      Fleet.FleetContradictionGapReclassificationPermission → ⊥

open GovernedLegalWorkflowComplianceTOEReceipt public

canonicalGovernedLegalWorkflowComplianceReceipt :
  GovernedLegalWorkflowComplianceTOEReceipt
canonicalGovernedLegalWorkflowComplianceReceipt =
  record
    { workflowHandoff =
        Workflow.canonicalGovernedLegalWorkflowTOEInvariantHandoff
    ; workflowHandoffIsCanonical = refl
    ; expertQualificationFirewall =
        expertQualificationDoesNotCreateForensicCompliance
    ; reportAdmissionMissingInputFirewall =
        reportAdmissionDoesNotRepairMissingInput
    ; legalReviewTruthFirewall =
        legalReviewDoesNotCreateClaimTruth
    ; officialSurfaceFineStateFirewall =
        officialLegalSurfaceDoesNotRecoverFineState
    ; legalityLegitimacyFirewall =
        legalityAloneDoesNotCreateLegitimacy
    ; actionstepStyleVendorIdentityCreatesAuthority =
        Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
          Domain.canonicalDomainTransportReceipt
    ; actionstepStyleVendorIdentityCreatesAuthorityIsFalse =
        refl
    ; actionstepStyleTargetNeedsOwnAuthorityWitness =
        Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
          Domain.canonicalDomainTransportReceipt
    ; actionstepStyleTargetNeedsOwnAuthorityWitnessIsTrue =
        refl
    ; ibrahimRecognitionBoundary =
        Ibrahim.ibrahimRecognitionParetoBoundary
    ; ibrahimSearchPriorityFirewall =
        Ibrahim.searchPriorityDoesNotCreateProof
    ; fleetFormalGapCount =
        Fleet.unformalisedFormalGaps Fleet.canonicalFleetFormalGapTargetReceipt
    ; fleetFormalGapCountIs58 = refl
    ; fleetDischargedCount =
        Fleet.dischargedCoreKnowledgeFibres Fleet.canonicalFleetFormalGapTargetReceipt
    ; fleetDischargedCountIs584 = refl
    ; fleetContradictionCount =
        Fleet.polarityContradictionGaps Fleet.canonicalFleetFormalGapTargetReceipt
    ; fleetContradictionCountIs44 = refl
    ; fleetPriorityFirewall =
        Fleet.fleetEigenPriorityDoesNotCreateProof
    ; fleetCountDischargeFirewall =
        Fleet.fleetExternalCountDoesNotCreateFormalDischarge
    ; fleetDischargedRetargetFirewall =
        Fleet.fleetDischargedFibresCannotBeRetargetedByThisBoundary
    ; fleetContradictionRelabelFirewall =
        Fleet.fleetContradictionsCannotBeRelabelledAsFormalGaps
    }
