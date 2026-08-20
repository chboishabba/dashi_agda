module DASHI.Environment.CertifiedValidationGovernanceExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- The base governance module is a runtime evidence carrier.  Its Bool fields
-- are not themselves proof that a deployment gate succeeded.  This module adds
-- the promotion layer: every condition used to authorize deployment is backed
-- by equality-to-true evidence, and validation-result lists can be certified as
-- all passed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Environment.ValidationGovernance as Governance


data AllValidationPassed : List Governance.ValidationResult → Set where
  allValidationPassedNil : AllValidationPassed []
  allValidationPassedCons :
    ∀ {result rest} →
    Governance.passed result ≡ true →
    AllValidationPassed rest →
    AllValidationPassed (result ∷ rest)

record CertifiedGovernanceReview
    (review : Governance.GovernanceReview) : Set where
  constructor certifiedGovernanceReview
  field
    validationsPassed :
      AllValidationPassed (Governance.validationResults review)
    communityReviewCheck : Governance.communityReviewRecorded review ≡ true
    uncertaintyDisclosureCheck : Governance.uncertaintyExposed review ≡ true
    missingDataDisclosureCheck : Governance.missingDataExposed review ≡ true

open CertifiedGovernanceReview public

record CertifiedDeploymentGate
    (gate : Governance.DeploymentGate) : Set where
  constructor certifiedDeploymentGate
  field
    reviewCertified : CertifiedGovernanceReview (Governance.governanceReview gate)
    hardConstraintsCheck : Governance.allHardConstraintsSatisfied gate ≡ true
    legalApprovalCheck : Governance.legalApprovalRecorded gate ≡ true
    ecologicalApprovalCheck : Governance.ecologicalApprovalRecorded gate ≡ true
    engineeringApprovalCheck : Governance.engineeringApprovalRecorded gate ≡ true
    communityApprovalCheck :
      Governance.communityApprovalRecordedWhereRequired gate ≡ true
    deploymentPermissionCheck : Governance.deploymentPermitted gate ≡ true

open CertifiedDeploymentGate public

record CertifiedGovernanceBoundary : Set where
  constructor certifiedGovernanceBoundary
  field
    rawBooleanGateDoesNotByItselfProveDeploymentEligibility : Bool
    everyListedValidationMustPassForThisPromotion : Bool
    disclosureChecksAreProofBearing : Bool
    approvalChecksAreProofBearing : Bool
    deploymentPermissionIsProofBearing : Bool

canonicalCertifiedGovernanceBoundary : CertifiedGovernanceBoundary
canonicalCertifiedGovernanceBoundary =
  certifiedGovernanceBoundary true true true true true
