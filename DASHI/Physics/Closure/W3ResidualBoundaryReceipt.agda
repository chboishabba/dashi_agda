module DASHI.Physics.Closure.W3ResidualBoundaryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Fermat / Kepler-class Lane 4 empirical validation boundary.
--
-- This receipt records the local 2026-05-12 t43 clean-freeze finalisation
-- attempt.  The runner executed and produced a projection artifact, but the
-- artifact itself still reports comparisonLawStatus = not-claimed and does
-- not compute chi2.  It also does not match the older recorded /tmp artifact
-- digests, and the current repo state is not the frozen commit/worktree.
--
-- Therefore this module is a residual boundary, not
-- W3PromotionCandidateFinalised.

data W3T43FinalisationStatus : Set where
  residualBoundaryBlocked :
    W3T43FinalisationStatus

data W3T43FinalisationBlocker : Set where
  runnerComparisonLawNotClaimed :
    W3T43FinalisationBlocker
  runnerChi2NotComputed :
    W3T43FinalisationBlocker
  chi2DofBoundNotEstablishedByArtifact :
    W3T43FinalisationBlocker
  observedArtifactDigestDoesNotMatchRecordedReceipts :
    W3T43FinalisationBlocker
  currentHeadDoesNotMatchFrozenCommit :
    W3T43FinalisationBlocker
  worktreeCleanCertificateNotAsserted :
    W3T43FinalisationBlocker
  acceptedAuthorityRouteMissing :
    W3T43FinalisationBlocker
  nonCollapseWitnessNotAuthorityAccepted :
    W3T43FinalisationBlocker
  acceptedEvidenceAuthorityTokenMissing :
    W3T43FinalisationBlocker

canonicalW3T43FinalisationBlockers :
  List W3T43FinalisationBlocker
canonicalW3T43FinalisationBlockers =
  runnerComparisonLawNotClaimed
  ∷ runnerChi2NotComputed
  ∷ chi2DofBoundNotEstablishedByArtifact
  ∷ observedArtifactDigestDoesNotMatchRecordedReceipts
  ∷ currentHeadDoesNotMatchFrozenCommit
  ∷ worktreeCleanCertificateNotAsserted
  ∷ acceptedAuthorityRouteMissing
  ∷ nonCollapseWitnessNotAuthorityAccepted
  ∷ acceptedEvidenceAuthorityTokenMissing
  ∷ []

record W3ResidualBoundaryReceipt : Set where
  field
    status :
      W3T43FinalisationStatus

    command :
      String

    outputArtifact :
      String

    outputArtifactSha256 :
      String

    observedProjectionDigest :
      String

    observedProjectionComplete :
      Bool

    observedComparisonLawStatus :
      String

    observedComparisonStatus :
      String

    observedChi2ComputedByRunner :
      Bool

    observedChi2DofBoundEstablished :
      Bool

    observedPerBinPayloadCount :
      String

    maxPullWitness :
      String

    nonCollapseWitnessAcceptedByAuthority :
      Bool

    t43DigestStatus :
      Bool

    t44DigestStatus :
      Bool

    requestedFreezeHash :
      String

    currentHead :
      String

    recordedPromotionCandidateArtifactSha256 :
      String

    recordedPromotionCandidateProjectionDigest :
      String

    recordedPerBinArtifactSha256 :
      String

    recordedPerBinProjectionDigest :
      String

    acceptedAuthorityRouteConstructed :
      Bool

    blockers :
      List W3T43FinalisationBlocker

    finalised :
      Bool

    promotesW3AcceptedAuthority :
      Bool

    noTokenFabricated :
      ⊤

    nonPromotionBoundary :
      List String

canonicalW3ResidualBoundaryReceipt :
  W3ResidualBoundaryReceipt
canonicalW3ResidualBoundaryReceipt =
  record
    { status =
        residualBoundaryBlocked
    ; command =
        "python3 scripts/run_t43_projection.py --freeze-hash 3205d746639568762c9e97adf4a3672c356bd491 --prediction-api DASHI.Physics.Prediction.sigma_dashi:predict_ratio --output logs/research/t43_clean_freeze_finalisation.json"
    ; outputArtifact =
        "logs/research/t43_clean_freeze_finalisation.json"
    ; outputArtifactSha256 =
        "5956b6bbdd30ef39840e5b2103263ea02134e4a317847cd54ae8a813c0e92cac"
    ; observedProjectionDigest =
        "e34cfa4c8cbebf6827c9401d95d179fb1d015507dcd9b8287ee772f613baa558"
    ; observedProjectionComplete =
        true
    ; observedComparisonLawStatus =
        "not-claimed"
    ; observedComparisonStatus =
        "not-computed"
    ; observedChi2ComputedByRunner =
        false
    ; observedChi2DofBoundEstablished =
        false
    ; observedPerBinPayloadCount =
        "18"
    ; maxPullWitness =
        "bin 12; pred 0.0486590199823977; data 0.049758; unc 0.00048197510309143566; pull -2.280159308132989"
    ; nonCollapseWitnessAcceptedByAuthority =
        false
    ; t43DigestStatus =
        true
    ; t44DigestStatus =
        true
    ; requestedFreezeHash =
        "3205d746639568762c9e97adf4a3672c356bd491"
    ; currentHead =
        "398595d85049b655d0ad0604d03ee70a1fed85b8"
    ; recordedPromotionCandidateArtifactSha256 =
        "ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac"
    ; recordedPromotionCandidateProjectionDigest =
        "00f6c23f97f9c0275d90e6ffbf6151b07defcc163708e2d93982d9b7d6866035"
    ; recordedPerBinArtifactSha256 =
        "3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0"
    ; recordedPerBinProjectionDigest =
        "cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79"
    ; acceptedAuthorityRouteConstructed =
        false
    ; blockers =
        canonicalW3T43FinalisationBlockers
    ; finalised =
        false
    ; promotesW3AcceptedAuthority =
        false
    ; noTokenFabricated =
        tt
    ; nonPromotionBoundary =
        "The local runner artifact is projection-complete but comparison-law-not-claimed"
        ∷ "The local runner artifact carries comparison.status not-computed, so chi2 is not runner-produced in this artifact"
        ∷ "The artifact does not establish a chi2/dof bound or per-bin comparison law"
        ∷ "The observed artifact digests do not match the older recorded /tmp clean-freeze receipts"
        ∷ "The current HEAD and dirty worktree do not satisfy the clean frozen-commit condition"
        ∷ "No accepted authority route or authority-accepted non-collapse witness is constructed here"
        ∷ "No W3AcceptedEvidenceAuthorityToken or W3AcceptedAuthorityExternalReceipt is constructed here"
        ∷ []
    }

canonicalW3ResidualBoundaryNotFinalised :
  W3ResidualBoundaryReceipt.finalised canonicalW3ResidualBoundaryReceipt
  ≡
  false
canonicalW3ResidualBoundaryNotFinalised = refl

canonicalW3ResidualBoundaryNoAuthorityPromotion :
  W3ResidualBoundaryReceipt.promotesW3AcceptedAuthority
    canonicalW3ResidualBoundaryReceipt
  ≡
  false
canonicalW3ResidualBoundaryNoAuthorityPromotion = refl

canonicalW3ResidualBoundaryNoChi2DofBound :
  W3ResidualBoundaryReceipt.observedChi2DofBoundEstablished
    canonicalW3ResidualBoundaryReceipt
  ≡
  false
canonicalW3ResidualBoundaryNoChi2DofBound = refl

canonicalW3ResidualBoundaryNoAcceptedAuthorityRoute :
  W3ResidualBoundaryReceipt.acceptedAuthorityRouteConstructed
    canonicalW3ResidualBoundaryReceipt
  ≡
  false
canonicalW3ResidualBoundaryNoAcceptedAuthorityRoute = refl
