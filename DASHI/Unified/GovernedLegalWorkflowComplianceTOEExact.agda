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
          Workflow.toeDomainTransportReceipt
    ; actionstepStyleVendorIdentityCreatesAuthorityIsFalse =
        Workflow.toeVendorIdentityDoesNotCreateAuthority
    ; actionstepStyleTargetNeedsOwnAuthorityWitness =
        Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
          Workflow.toeDomainTransportReceipt
    ; actionstepStyleTargetNeedsOwnAuthorityWitnessIsTrue =
        Workflow.toeTargetDomainNeedsOwnAuthorityWitness
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
