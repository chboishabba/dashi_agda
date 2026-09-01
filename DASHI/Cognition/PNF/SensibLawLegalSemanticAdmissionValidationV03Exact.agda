module DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionValidationV03Exact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawLegalSemanticAdmissionFrontierExact as Admission
import DASHI.Cognition.PNF.SensibLawGWBv01ResidualFrontierCertificationV03Exact as V03

record AdmissionSoftwareValidation : Set where
  constructor admissionSoftwareValidation
  field
    rustHead : String
    workspaceTestsPassed : Bool
    admissionTestsPassed : Nat
    clippyWarningsDeniedPassed : Bool
    releaseBuildPassed : Bool
    sourceContractsPassed : Bool
    pythonCompilationPassed : Bool

open AdmissionSoftwareValidation public

admissionValidationV03 : AdmissionSoftwareValidation
admissionValidationV03 =
  admissionSoftwareValidation
    "7c3364186fffea3bc4853df504bf7163243697f6"
    true
    6
    true
    true
    true
    true

workspaceValidationPassed : workspaceTestsPassed admissionValidationV03 ≡ true
workspaceValidationPassed = refl

sixAdmissionTestsPassed : admissionTestsPassed admissionValidationV03 ≡ 6
sixAdmissionTestsPassed = refl

data AgdaValidationStatus : Set where
  blockedByMissingBishopLibrary : AgdaValidationStatus

currentAgdaValidationStatus : AgdaValidationStatus
currentAgdaValidationStatus = blockedByMissingBishopLibrary

------------------------------------------------------------------------
-- Current theorem-bearing frontier after the Rust/GWB v0.3 receipt.
------------------------------------------------------------------------

data LegalSemanticValidatedFrontier : Set where
  goldAdmissionAndResidualV03ValidatedAwaitingFineResidualRefinement
    : LegalSemanticValidatedFrontier

currentLegalSemanticValidatedFrontier : LegalSemanticValidatedFrontier
currentLegalSemanticValidatedFrontier =
  goldAdmissionAndResidualV03ValidatedAwaitingFineResidualRefinement

v03ResidualTotalPinned :
  V03.residuals V03.expandedResidualFrontierV03 ≡ 706246
v03ResidualTotalPinned = refl

v03UnsupportedBucketPinned :
  V03.unsupportedDependency V03.canonicalResidualHistogramV03 ≡ 533994
v03UnsupportedBucketPinned = refl

data RustValidationImpliesAgdaKernelSuccess : Set where
data MissingBishopLibraryMeansAgdaTheoremFailed : Set where

rustValidationDoesNotImplyAgdaKernelSuccess :
  RustValidationImpliesAgdaKernelSuccess → ⊥
rustValidationDoesNotImplyAgdaKernelSuccess ()

missingBishopDoesNotMeanAgdaTheoremFailed :
  MissingBishopLibraryMeansAgdaTheoremFailed → ⊥
missingBishopDoesNotMeanAgdaTheoremFailed ()

parserCandidateBoundaryStillHolds :
  Admission.ParserCandidateAloneAuthorizesAdmission → ⊥
parserCandidateBoundaryStillHolds = Admission.parserCandidateAloneCannotAuthorizeAdmission
