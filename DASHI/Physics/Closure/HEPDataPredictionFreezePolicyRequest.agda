module DASHI.Physics.Closure.HEPDataPredictionFreezePolicyRequest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataPredictionFreezeIdentityDiagnostic as FreezeIdentity

------------------------------------------------------------------------
-- HEP-R30: clean predictionFixedAt policy/request surface.
--
-- This module records the user-supplied clean-freeze process shape only:
-- clean via stash/commit, run rev-parse HEAD, and make the runner consume
-- that hash.  It does not run git stash, commit, rev-parse, or a projection
-- runner, and it does not accept the current dirty HEAD as predictionFixedAt.

data HEPDataPredictionFreezePolicyStatus : Set where
  blockedAwaitingCleanWorktreeAndDigestBoundArtifact :
    HEPDataPredictionFreezePolicyStatus

data HEPDataCleanFreezeStep : Set where
  cleanWorktreeViaStashOrCommit :
    HEPDataCleanFreezeStep
  revParseHeadAfterCleanWorktree :
    HEPDataCleanFreezeStep
  runnerUsesRevParsedHeadHash :
    HEPDataCleanFreezeStep

canonicalHEPDataCleanFreezeSequence :
  List HEPDataCleanFreezeStep
canonicalHEPDataCleanFreezeSequence =
  cleanWorktreeViaStashOrCommit
  ∷ revParseHeadAfterCleanWorktree
  ∷ runnerUsesRevParsedHeadHash
  ∷ []

data HEPDataWorktreeCleanCertificateField : Set where
  cleanWorktreeCertificate :
    HEPDataWorktreeCleanCertificateField
  revParseHeadHash :
    HEPDataWorktreeCleanCertificateField
  runnerHashBinding :
    HEPDataWorktreeCleanCertificateField
  frozenPredictionArtifactDigest :
    HEPDataWorktreeCleanCertificateField

canonicalHEPDataWorktreeCleanCertificateShape :
  List HEPDataWorktreeCleanCertificateField
canonicalHEPDataWorktreeCleanCertificateShape =
  cleanWorktreeCertificate
  ∷ revParseHeadHash
  ∷ runnerHashBinding
  ∷ frozenPredictionArtifactDigest
  ∷ []

data HEPDataPredictionFreezePolicyBoundary : Set where
  noGitStashOrCommitHere :
    HEPDataPredictionFreezePolicyBoundary
  noRevParseExecutionHere :
    HEPDataPredictionFreezePolicyBoundary
  noDirtyHeadAcceptanceHere :
    HEPDataPredictionFreezePolicyBoundary
  noFrozenPredictionArtifactHere :
    HEPDataPredictionFreezePolicyBoundary
  noAcceptedFreezeReceiptHere :
    HEPDataPredictionFreezePolicyBoundary
  noHEPR30PromotionHere :
    HEPDataPredictionFreezePolicyBoundary

canonicalHEPDataPredictionFreezePolicyBoundaries :
  List HEPDataPredictionFreezePolicyBoundary
canonicalHEPDataPredictionFreezePolicyBoundaries =
  noGitStashOrCommitHere
  ∷ noRevParseExecutionHere
  ∷ noDirtyHeadAcceptanceHere
  ∷ noFrozenPredictionArtifactHere
  ∷ noAcceptedFreezeReceiptHere
  ∷ noHEPR30PromotionHere
  ∷ []

data HEPDataAcceptedCleanPredictionFreezeReceipt : Set where

acceptedCleanPredictionFreezeReceiptImpossibleHere :
  HEPDataAcceptedCleanPredictionFreezeReceipt →
  ⊥
acceptedCleanPredictionFreezeReceiptImpossibleHere ()

record HEPDataPredictionFreezePolicyRequest : Setω where
  field
    policyStatus :
      HEPDataPredictionFreezePolicyStatus

    priorDirtyIdentityDiagnostic :
      FreezeIdentity.HEPDataPredictionFreezeIdentityDiagnostic

    diagnosticHeadOnly :
      String

    cleanFreezeSequence :
      List HEPDataCleanFreezeStep

    cleanFreezeSequenceIsCanonical :
      cleanFreezeSequence ≡ canonicalHEPDataCleanFreezeSequence

    exactCleanFreezeSequenceText :
      List String

    worktreeCleanCertificateShape :
      List HEPDataWorktreeCleanCertificateField

    worktreeCleanCertificateShapeIsCanonical :
      worktreeCleanCertificateShape
      ≡
      canonicalHEPDataWorktreeCleanCertificateShape

    exactWorktreeCleanCertificateShapeText :
      List String

    missingInputs :
      List String

    nonPromotionBoundary :
      List HEPDataPredictionFreezePolicyBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary
      ≡
      canonicalHEPDataPredictionFreezePolicyBoundaries

    acceptedFreezeReceiptBlocked :
      HEPDataAcceptedCleanPredictionFreezeReceipt →
      ⊥

canonicalHEPDataPredictionFreezePolicyRequest :
  HEPDataPredictionFreezePolicyRequest
canonicalHEPDataPredictionFreezePolicyRequest =
  record
    { policyStatus =
        blockedAwaitingCleanWorktreeAndDigestBoundArtifact
    ; priorDirtyIdentityDiagnostic =
        FreezeIdentity.canonicalHEPDataPredictionFreezeIdentityDiagnostic
    ; diagnosticHeadOnly =
        "e137415fe60aa470b9cd41d2357d9494592c0cec is diagnostic-only and is not accepted as predictionFixedAt while the worktree is dirty"
    ; cleanFreezeSequence =
        canonicalHEPDataCleanFreezeSequence
    ; cleanFreezeSequenceIsCanonical =
        refl
    ; exactCleanFreezeSequenceText =
        "clean via stash/commit"
        ∷ "rev-parse HEAD"
        ∷ "runner uses that hash"
        ∷ []
    ; worktreeCleanCertificateShape =
        canonicalHEPDataWorktreeCleanCertificateShape
    ; worktreeCleanCertificateShapeIsCanonical =
        refl
    ; exactWorktreeCleanCertificateShapeText =
        "worktree-clean certificate: no modified or untracked files at the freeze point"
        ∷ "rev-parse HEAD hash captured after the clean-worktree certificate"
        ∷ "runner input binds exactly to that rev-parse HEAD hash"
        ∷ "frozen prediction artifact digest binds the runner output before HEPData comparison"
        ∷ []
    ; missingInputs =
        "clean worktree"
        ∷ "rev-parse HEAD output captured after the clean state"
        ∷ "runner execution bound to that hash"
        ∷ "digest-bound frozen prediction artifact"
        ∷ []
    ; nonPromotionBoundary =
        canonicalHEPDataPredictionFreezePolicyBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; acceptedFreezeReceiptBlocked =
        acceptedCleanPredictionFreezeReceiptImpossibleHere
    }

canonicalHEPDataPredictionFreezePolicyStatus :
  HEPDataPredictionFreezePolicyStatus
canonicalHEPDataPredictionFreezePolicyStatus =
  blockedAwaitingCleanWorktreeAndDigestBoundArtifact
