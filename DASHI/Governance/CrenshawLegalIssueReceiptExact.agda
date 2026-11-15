module DASHI.Governance.CrenshawLegalIssueReceiptExact where

-- An issue/holding receipt is indexed by exact case, stage, and issue.
-- A court-text locator is NOT an authenticated source receipt.
-- Validation predicates are supplied by the external case auditor;
-- no constructor here manufactures their evidence.
open import DASHI.Core.Prelude
import DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact as Case

data CaseIssue : Set where
  combinedCause appellateDisposition factualLiability remedialOrder : CaseIssue

data ReceiptPurpose : Set where
  sourceTextLocation officialArtifactVerification passageVerified
  legalApplicationEvaluation : ReceiptPurpose

record ExternalCaseChecks : Set₁ where
  field
    CourtArtifact : Case.CaseKey → Case.CourtStage → Set
    PassageCorresponds :
      (c : Case.CaseKey) (s : Case.CourtStage)
      (t : Case.BoundedLegalTopic) → Set
    NoContraryHoldingOmitted :
      (c : Case.CaseKey) (s : Case.CourtStage)
      (t : Case.BoundedLegalTopic) → Set

open ExternalCaseChecks public

record AuthenticatedCasePassage
  (checks : ExternalCaseChecks)
  (c : Case.CaseKey)
  (s : Case.CourtStage)
  (t : Case.BoundedLegalTopic) : Set where
  constructor authenticated-case-passage
  field
    located : Case.ReportedCasePassage c s t
    originalArtifact : CourtArtifact checks c s
    sourceAlignment : PassageCorresponds checks c s t
    contraryReasonsChecked : NoContraryHoldingOmitted checks c s t

open AuthenticatedCasePassage public

authenticatedRequiresOriginalArtifact :
  (checks : ExternalCaseChecks)
  (c : Case.CaseKey) (s : Case.CourtStage)
  (t : Case.BoundedLegalTopic) →
  AuthenticatedCasePassage checks c s t →
  CourtArtifact checks c s
authenticatedRequiresOriginalArtifact checks c s t = originalArtifact

authenticatedRequiresPassageCorrespondence :
  (checks : ExternalCaseChecks)
  (c : Case.CaseKey) (s : Case.CourtStage)
  (t : Case.BoundedLegalTopic) →
  AuthenticatedCasePassage checks c s t →
  PassageCorresponds checks c s t
authenticatedRequiresPassageCorrespondence checks c s t = sourceAlignment

authenticatedRequiresContraryReasonReview :
  (checks : ExternalCaseChecks)
  (c : Case.CaseKey) (s : Case.CourtStage)
  (t : Case.BoundedLegalTopic) →
  AuthenticatedCasePassage checks c s t →
  NoContraryHoldingOmitted checks c s t
authenticatedRequiresContraryReasonReview checks c s t = contraryReasonsChecked

-- A synthetic negative control: even a known located district passage does
-- not supply the independent verified-original-artifact predicate.
noVerifiedOriginalControl : ExternalCaseChecks
noVerifiedOriginalControl = record
  { CourtArtifact = λ c s → ⊥
  ; PassageCorresponds = λ c s t → ⊤
  ; NoContraryHoldingOmitted = λ c s t → ⊤
  }

unverifiedLocatorCannotAdmitDistrictHolding :
  AuthenticatedCasePassage
    noVerifiedOriginalControl
    Case.deGraffenreid
    Case.districtCourt
    Case.combinationClaimRejected → ⊥
unverifiedLocatorCannotAdmitDistrictHolding receipt =
  originalArtifact receipt

unverifiedLocatorCannotAdmitJefferiesHolding :
  AuthenticatedCasePassage
    noVerifiedOriginalControl
    Case.jefferies
    Case.appellateCourt
    Case.combinationClaimRecognised → ⊥
unverifiedLocatorCannotAdmitJefferiesHolding receipt =
  originalArtifact receipt

-- No construction from a located passage alone to an authenticated one
-- is provided; court-level proof data has to come from original sources.
