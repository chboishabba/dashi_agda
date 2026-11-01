module DASHI.Physics.Closure.HEPDataPredictionFreezeIdentityDiagnostic where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- HEP-R26: prediction freeze identity diagnostic.
--
-- This module records the current freeze identity status only.  HEAD may be
-- named, but the dirty worktree blocks any accepted predictionFixedAt receipt.
-- It does not clean the tree, compute an artifact digest, accept a freeze, or
-- promote HEP-R26.

data HEPDataPredictionFreezeIdentityStatus : Set where
  blockedDirtyWorktreePreventsAcceptedPredictionFixedAt :
    HEPDataPredictionFreezeIdentityStatus

data HEPDataPredictionFreezeDirtyStateLabel : Set where
  dirtyModifiedAndUntrackedWorktree :
    HEPDataPredictionFreezeDirtyStateLabel

data HEPDataPredictionFreezePolicy : Set where
  requireCleanWorktreeForAcceptedFreeze :
    HEPDataPredictionFreezePolicy

data HEPDataPredictionFreezeArtifactDigestRequirement : Set where
  requireDigestBoundFrozenPredictionArtifact :
    HEPDataPredictionFreezeArtifactDigestRequirement

data HEPDataAcceptedPredictionFreezeReceipt : Set where

acceptedPredictionFreezeReceiptImpossibleHere :
  HEPDataAcceptedPredictionFreezeReceipt →
  ⊥
acceptedPredictionFreezeReceiptImpossibleHere ()

data HEPDataPredictionFreezeIdentityBoundary : Set where
  noCleanFreezeClaimHere :
    HEPDataPredictionFreezeIdentityBoundary
  noPredictionFixedAtReceiptHere :
    HEPDataPredictionFreezeIdentityBoundary
  noArtifactDigestReceiptHere :
    HEPDataPredictionFreezeIdentityBoundary
  noHEPR26PromotionHere :
    HEPDataPredictionFreezeIdentityBoundary

canonicalHEPDataPredictionFreezeIdentityBoundaries :
  List HEPDataPredictionFreezeIdentityBoundary
canonicalHEPDataPredictionFreezeIdentityBoundaries =
  noCleanFreezeClaimHere
  ∷ noPredictionFixedAtReceiptHere
  ∷ noArtifactDigestReceiptHere
  ∷ noHEPR26PromotionHere
  ∷ []

record HEPDataPredictionFreezeIdentityDiagnostic : Setω where
  field
    status :
      HEPDataPredictionFreezeIdentityStatus

    headCommitString :
      String

    dirtyStateLabel :
      HEPDataPredictionFreezeDirtyStateLabel

    dirtyStateText :
      String

    requiredCleanFreezePolicy :
      HEPDataPredictionFreezePolicy

    requiredCleanFreezePolicyText :
      String

    artifactDigestRequirement :
      HEPDataPredictionFreezeArtifactDigestRequirement

    artifactDigestRequirementText :
      String

    acceptedFreezeReceipt :
      HEPDataAcceptedPredictionFreezeReceipt →
      ⊥

    nonPromotionBoundary :
      List HEPDataPredictionFreezeIdentityBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataPredictionFreezeIdentityBoundaries

    diagnosticNotes :
      List String

canonicalHEPDataPredictionFreezeIdentityDiagnostic :
  HEPDataPredictionFreezeIdentityDiagnostic
canonicalHEPDataPredictionFreezeIdentityDiagnostic =
  record
    { status =
        blockedDirtyWorktreePreventsAcceptedPredictionFixedAt
    ; headCommitString =
        "e137415fe60aa470b9cd41d2357d9494592c0cec"
    ; dirtyStateLabel =
        dirtyModifiedAndUntrackedWorktree
    ; dirtyStateText =
        "dirty: modified and untracked files are present in the worktree"
    ; requiredCleanFreezePolicy =
        requireCleanWorktreeForAcceptedFreeze
    ; requiredCleanFreezePolicyText =
        "accepted predictionFixedAt requires a clean worktree at the named HEAD commit"
    ; artifactDigestRequirement =
        requireDigestBoundFrozenPredictionArtifact
    ; artifactDigestRequirementText =
        "accepted freeze requires a digest-bound frozen prediction artifact"
    ; acceptedFreezeReceipt =
        acceptedPredictionFreezeReceiptImpossibleHere
    ; nonPromotionBoundary =
        canonicalHEPDataPredictionFreezeIdentityBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; diagnosticNotes =
        "HEAD may be named for diagnostic identity only"
        ∷ "The dirty worktree prevents accepted predictionFixedAt"
        ∷ "No artifact digest is supplied by this module"
        ∷ "No HEP-R26 promotion is performed by this module"
        ∷ []
    }

canonicalHEPDataPredictionFreezeIdentityStatus :
  HEPDataPredictionFreezeIdentityStatus
canonicalHEPDataPredictionFreezeIdentityStatus =
  blockedDirtyWorktreePreventsAcceptedPredictionFixedAt

canonicalHEPDataPredictionFreezeIdentityReceiptImpossible :
  HEPDataAcceptedPredictionFreezeReceipt →
  ⊥
canonicalHEPDataPredictionFreezeIdentityReceiptImpossible =
  acceptedPredictionFreezeReceiptImpossibleHere
