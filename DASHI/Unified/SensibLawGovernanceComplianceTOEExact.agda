{-# OPTIONS --safe #-}
module DASHI.Unified.SensibLawGovernanceComplianceTOEExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Unified.SensibLawGovernanceTOEExact as Governance
import DASHI.Unified.FleetFormalGapTargetTOEExact as Fleet
import DASHI.Unified.BalabanIbrahimParetoSnowballTOEExact as Ibrahim
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review
import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed
import DASHI.Governance.LegalDecisionDoubleProjectionExact as LegalDecision
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

------------------------------------------------------------------------
-- LEGAL-COMPLIANCE FIREWALL EXTENSION OF THE CANONICAL SENSIBLAW TOE OWNER.
--
-- Reuse the #1323 governance normalization.
-- Add only source-owned firewalls that the base facade does not expose.
-- Do not create an Actionstep ontology.
-- Do not infer legal authority from vendor identity or workflow state.
------------------------------------------------------------------------

QualificationAutomaticallyForensicCompliance : Set
QualificationAutomaticallyForensicCompliance =
  Expert.QualificationAutomaticallyForensicCompliance

LegalReviewDecisionCreatesApplicability : Set
LegalReviewDecisionCreatesApplicability =
  Review.LegalReviewDecisionCreatesApplicability

LegalReviewDecisionCreatesClaimTruth : Set
LegalReviewDecisionCreatesClaimTruth =
  Review.LegalReviewDecisionCreatesClaimTruth

ParserCandidateAloneAuthorizesAdmission : Set
ParserCandidateAloneAuthorizesAdmission =
  Admission.ParserCandidateAloneAuthorizesAdmission

OfficialLegalSurfaceRecoversFineState : Set
OfficialLegalSurfaceRecoversFineState =
  NF.FactorsThrough LegalDecision.officialSurface LegalDecision.fineLegalStateOf

LegalOnlyCreatesLegitimacy : Set₁
LegalOnlyCreatesLegitimacy =
  Legitimacy.AdmittedLegitimacy Legitimacy.demoEvidence Legitimacy.legalOnly

sensibLawQualificationDoesNotCreateForensicCompliance :
  QualificationAutomaticallyForensicCompliance → ⊥
sensibLawQualificationDoesNotCreateForensicCompliance =
  Expert.qualificationDoesNotAutomaticallyProveForensicCompliance

sensibLawReportAdmissionDoesNotRepairMissingInput :
  Expert.ReportAdmissionRepairsMissingInput → ⊥
sensibLawReportAdmissionDoesNotRepairMissingInput =
  Expert.reportAdmissionDoesNotRepairMissingInput

sensibLawReviewDoesNotCreateApplicability :
  LegalReviewDecisionCreatesApplicability → ⊥
sensibLawReviewDoesNotCreateApplicability =
  Review.legalReviewDecisionDoesNotCreateApplicability

sensibLawReviewDoesNotCreateClaimTruth :
  LegalReviewDecisionCreatesClaimTruth → ⊥
sensibLawReviewDoesNotCreateClaimTruth =
  Review.legalReviewDecisionDoesNotCreateClaimTruth

sensibLawParserCandidateDoesNotAuthorizeAdmission :
  ParserCandidateAloneAuthorizesAdmission → ⊥
sensibLawParserCandidateDoesNotAuthorizeAdmission =
  Admission.parserCandidateAloneCannotAuthorizeAdmission

sensibLawOfficialSurfaceDoesNotRecoverFineLegalState :
  OfficialLegalSurfaceRecoversFineState → ⊥
sensibLawOfficialSurfaceDoesNotRecoverFineLegalState =
  LegalDecision.officialSurfaceCannotRecoverFineLegalState

sensibLawOfficialActionDoesNotRecoverAutonomyAndAuthority :
  NF.FactorsThrough
    LegalDecision.autonomyOfficialSurface
    LegalDecision.fineAutonomyLegalStateOf
  → ⊥
sensibLawOfficialActionDoesNotRecoverAutonomyAndAuthority =
  LegalDecision.officialActionCannotRecoverAutonomyAndAuthority

sensibLawLegalityAloneDoesNotCreateLegitimacy :
  LegalOnlyCreatesLegitimacy → ⊥
sensibLawLegalityAloneDoesNotCreateLegitimacy =
  Legitimacy.legalOnlyIsNotAdmittedLegitimacy

sensibLawMissingAdmissibilityAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
  ≡ Governed.abstain
sensibLawMissingAdmissibilityAbstains =
  Promotion.missingAdmissibilityAbstains

sensibLawMissingValidationAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
  ≡ Governed.abstain
sensibLawMissingValidationAbstains =
  Promotion.missingValidationAbstains

------------------------------------------------------------------------
-- Fleet target discipline.
------------------------------------------------------------------------

record SensibLawGovernanceComplianceTOEReceipt : Set₁ where
  field
    governanceFrame : Governance.SensibLawGovernanceTOEZKPFrame
    governanceFrameIsCanonical :
      governanceFrame ≡ Governance.canonicalSensibLawGovernanceTOEZKPFrame

    expertQualificationFirewall :
      QualificationAutomaticallyForensicCompliance → ⊥
    reviewApplicabilityFirewall :
      LegalReviewDecisionCreatesApplicability → ⊥
    reviewTruthFirewall :
      LegalReviewDecisionCreatesClaimTruth → ⊥
    parserAdmissionFirewall :
      ParserCandidateAloneAuthorizesAdmission → ⊥
    officialSurfaceFirewall :
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
    ibrahimSearchPriorityDoesNotCreateProof :
      Ibrahim.SearchPriorityCreatesProof → ⊥

    fleetFormalGapCount : Nat
    fleetFormalGapCountIs58 : fleetFormalGapCount ≡ 58
    fleetDischargedCount : Nat
    fleetDischargedCountIs584 : fleetDischargedCount ≡ 584
    fleetContradictionCount : Nat
    fleetContradictionCountIs44 : fleetContradictionCount ≡ 44

    fleetPriorityDoesNotCreateProof :
      Fleet.FleetEigenPriorityCreatesProof → ⊥
    fleetCountDoesNotCreateDischarge :
      Fleet.FleetExternalCountCreatesFormalDischarge → ⊥
    dischargedFibresCannotBeRetargeted :
      Fleet.FleetDischargedFibreRetargetPermission → ⊥
    contradictionGapsCannotBeRelabelled :
      Fleet.FleetContradictionGapReclassificationPermission → ⊥

open SensibLawGovernanceComplianceTOEReceipt public

canonicalSensibLawGovernanceComplianceReceipt :
  SensibLawGovernanceComplianceTOEReceipt
canonicalSensibLawGovernanceComplianceReceipt =
  record
    { governanceFrame =
        Governance.canonicalSensibLawGovernanceTOEZKPFrame
    ; governanceFrameIsCanonical = refl
    ; expertQualificationFirewall =
        sensibLawQualificationDoesNotCreateForensicCompliance
    ; reviewApplicabilityFirewall =
        sensibLawReviewDoesNotCreateApplicability
    ; reviewTruthFirewall =
        sensibLawReviewDoesNotCreateClaimTruth
    ; parserAdmissionFirewall =
        sensibLawParserCandidateDoesNotAuthorizeAdmission
    ; officialSurfaceFirewall =
        sensibLawOfficialSurfaceDoesNotRecoverFineLegalState
    ; legalityLegitimacyFirewall =
        sensibLawLegalityAloneDoesNotCreateLegitimacy
    ; actionstepStyleVendorIdentityCreatesAuthority =
        Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
          Governance.governanceDomainTransportReceipt
    ; actionstepStyleVendorIdentityCreatesAuthorityIsFalse =
        Governance.governanceVendorIdentityDoesNotCreateAuthority
    ; actionstepStyleTargetNeedsOwnAuthorityWitness =
        Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
          Governance.governanceDomainTransportReceipt
    ; actionstepStyleTargetNeedsOwnAuthorityWitnessIsTrue =
        Governance.governanceTargetDomainNeedsOwnAuthorityWitness
    ; ibrahimRecognitionBoundary =
        Ibrahim.ibrahimRecognitionParetoBoundary
    ; ibrahimSearchPriorityDoesNotCreateProof =
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
    ; fleetPriorityDoesNotCreateProof =
        Fleet.fleetEigenPriorityDoesNotCreateProof
    ; fleetCountDoesNotCreateDischarge =
        Fleet.fleetExternalCountDoesNotCreateFormalDischarge
    ; dischargedFibresCannotBeRetargeted =
        Fleet.fleetDischargedFibresCannotBeRetargetedByThisBoundary
    ; contradictionGapsCannotBeRelabelled =
        Fleet.fleetContradictionsCannotBeRelabelledAsFormalGaps
    }
