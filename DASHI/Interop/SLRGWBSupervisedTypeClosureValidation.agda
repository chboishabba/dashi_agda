module DASHI.Interop.SLRGWBSupervisedTypeClosureValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Interop.SLRGWBSupervisedTypeClosureExact

validationRevisionPinned :
  everyFetchedNodeRevisionPinned canonicalSupervisedTypeClosureBoundary ≡ true
validationRevisionPinned = refl

validationP31SeedsClosure :
  p31SeedsInstanceTypeClosure canonicalSupervisedTypeClosureBoundary ≡ true
validationP31SeedsClosure = refl

validationP279SeedsClosure :
  p279SeedsSuperclassClosure canonicalSupervisedTypeClosureBoundary ≡ true
validationP279SeedsClosure = refl

validationBoundedP279 :
  recursiveP279TraversalIsBounded canonicalSupervisedTypeClosureBoundary ≡ true
validationBoundedP279 = refl

validationObservedAbsenceNotGlobal :
  observedAbsenceMeansGlobalAbsence canonicalSupervisedTypeClosureBoundary ≡ false
validationObservedAbsenceNotGlobal = refl

validationTruncationAbstains :
  truncationMayPromoteClassification canonicalSupervisedTypeClosureBoundary ≡ false
validationTruncationAbstains = refl

validationMultiRevisionNotSnapshot :
  multiRevisionManifestIsSimultaneousSnapshot canonicalSupervisedTypeClosureBoundary ≡ false
validationMultiRevisionNotSnapshot = refl

validationProviderDoesNotPay :
  providerDispositionPaysResidual canonicalSupervisedTypeClosureBoundary ≡ false
validationProviderDoesNotPay = refl

validationReviewRequired :
  reviewRequiredForWorldDelta canonicalSupervisedTypeClosureBoundary ≡ true
validationReviewRequired = refl

validationInstancePressure :
  p31OnlyMayCreateInstanceShapedSuperclassPressure
    canonicalSupervisedTypeClosureBoundary ≡ true
validationInstancePressure = refl

validationInstancePressureNotWrongType :
  instanceShapedPressureIsAutomaticWrongType
    canonicalSupervisedTypeClosureBoundary ≡ false
validationInstancePressureNotWrongType = refl

validationLeanClosureExactness :
  leanWorkerProvidesExecutableClosureExactness
    canonicalSupervisedTypeClosureBoundary ≡ true
validationLeanClosureExactness = refl

validationLeanNotEvidenceAuthority :
  leanWorkerChecksLiveEvidenceAuthority
    canonicalSupervisedTypeClosureBoundary ≡ false
validationLeanNotEvidenceAuthority = refl

validationNatObservedAbsence :
  reusesNatObservedAbsenceDiscipline canonicalSupervisedTypeClosureBoundary ≡ true
validationNatObservedAbsence = refl

validationClimateHold :
  reusesClimateHoldOnDimensionalMismatch canonicalSupervisedTypeClosureBoundary ≡ true
validationClimateHold = refl

validationCandidateOnly :
  providerCandidateOnly canonicalSupervisedTypeClosureBoundary ≡ true
validationCandidateOnly = refl

validationNoAuthority :
  providerCreatesSemanticAuthority canonicalSupervisedTypeClosureBoundary ≡ false
validationNoAuthority = refl

validationNoApplicability :
  providerPromotesApplicability canonicalSupervisedTypeClosureBoundary ≡ false
validationNoApplicability = refl

validationNoTruth :
  providerPromotesClaimTruth canonicalSupervisedTypeClosureBoundary ≡ false
validationNoTruth = refl
