module DASHI.Environment.ValidationGovernance where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.InversePlanning as Planning
import DASHI.Environment.SurrogateCalibration as Surrogate

------------------------------------------------------------------------
-- Validation programmes.

data ValidationKind : Set where
  hindcast : ValidationKind
  pollutionReconstruction : ValidationKind
  expertPlanComparison : ValidationKind
  counterfactual : ValidationKind
  sensitivityAnalysis : ValidationKind
  conservationAudit : ValidationKind
  spatialHoldout : ValidationKind
  temporalHoldout : ValidationKind

record ValidationCase : Set where
  constructor mkValidationCase
  field
    caseName : String
    kind : ValidationKind
    inputManifest : List String
    expectedObservations : List String
    acceptanceCriteria : List String
    excludedClaims : List String
    independentData : Bool
open ValidationCase public

record ValidationResult : Set where
  constructor mkValidationResult
  field
    case : ValidationCase
    passed : Bool
    measuredErrors : List String
    failedCriteria : List String
    missingData : List String
    sensitivityFindings : List String
    provenance : List String
open ValidationResult public

record CommunityConstraint : Set where
  constructor mkCommunityConstraint
  field
    constraintName : String
    communityOrCustodian : String
    spatialScope : String
    temporalScope : String
    consentReference : String
    permittedUses : List String
    prohibitedUses : List String
    currentlyActive : Bool
open CommunityConstraint public

record GovernanceReview : Set where
  constructor mkGovernanceReview
  field
    planningReceipt : Planning.PlanningReceipt
    validationResults : List ValidationResult
    communityConstraints : List CommunityConstraint
    ecologicalReviewer : String
    engineeringReviewer : String
    policyReviewer : String
    communityReviewRecorded : Bool
    uncertaintyExposed : Bool
    missingDataExposed : Bool
    approvalStatus : String
open GovernanceReview public

record DeploymentGate : Set where
  constructor mkDeploymentGate
  field
    authoritativeVerification : Surrogate.SurrogateUseReceipt
    governanceReview : GovernanceReview
    allHardConstraintsSatisfied : Bool
    legalApprovalRecorded : Bool
    ecologicalApprovalRecorded : Bool
    engineeringApprovalRecorded : Bool
    communityApprovalRecordedWhereRequired : Bool
    deploymentPermitted : Bool
open DeploymentGate public

record ValidationGovernanceBoundary : Set where
  constructor mkValidationGovernanceBoundary
  field
    validationFailureCannotBeHidden : Bool
    sourceRankingIsNotLegalAttribution : Bool
    expertAgreementIsNotProof : Bool
    communityConstraintsAreFirstClass : Bool
    missingDataMustRemainVisible : Bool
    deploymentRequiresSeparateApproval : Bool
open ValidationGovernanceBoundary public

canonicalValidationGovernanceBoundary : ValidationGovernanceBoundary
canonicalValidationGovernanceBoundary =
  mkValidationGovernanceBoundary true true true true true true
