module DASHI.Research.OpenAIMath.OpenAIYangMills2026SourceIntakeExact where

-- External attribution: OpenAI, Wilson Yang--Mills construction,
-- 28 October 2026 submission, Apache-2.0,
-- https://github.com/yang-mills-group/OpenAI-YM-20261028
-- public Git commit 3456e5e75cf8d4cd558955a5c7638fba2d68f464.
-- Independent review: Douglas, Gross (chair), Jaffe, Klebanov, Nekrasov,
-- 10 November 2026 assessment, at
-- https://github.com/yang-mills-group/YM
-- commit 55ba9fc36293b3f4d52c6b1f813169a0be76ee98.
-- This is a SOURCE RECEIPT, not a Lean-to-Agda theorem import.
-- Original openai/math corpus source owner is distinct and imported below.
-- Proof attribution, chronology, trust, and actual source identity are separate.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import DASHI.Research.OpenAIMath.OpenAIMathUpstreamReceiptExact as Corpus
open import DASHI.Research.OpenAIMath.OpenAIMathSourceAtlasExact as Atlas

sourceRepository : String
sourceRepository = "https://github.com/yang-mills-group/OpenAI-YM-20261028"

sourceGitCommit : String
sourceGitCommit = "3456e5e75cf8d4cd558955a5c7638fba2d68f464"

reviewRepository : String
reviewRepository = "https://github.com/yang-mills-group/YM"

reviewGitCommit : String
reviewGitCommit = "55ba9fc36293b3f4d52c6b1f813169a0be76ee98"

sourceLean : String
sourceLean = "leanprover/lean4:v4.32.0"

dashiLeanWorldVersion : String
dashiLeanWorldVersion = "leanprover/lean4:v4.28.0"

originalOpenAIMathCorpusCommit : String
originalOpenAIMathCorpusCommit = Corpus.upstreamCommit

originalMathAtlasYMRoute : Atlas.DASHIProgramme
originalMathAtlasYMRoute = Atlas.yangMills

data ExternalYMClaim : Set where
  jointExistence : ExternalYMClaim
  reviewedCombinedAcceptance : ExternalYMClaim
  reviewedOPE : ExternalYMClaim

record ExternalYMProofSource : Set where
  constructor ymProofSource
  field
    claim : ExternalYMClaim
    repository : String
    commit : String
    modulePath : String
    declaration : String
    reviewerScope : String
    dashiOriginalSourceOwner : String

originalJointExistenceReceipt : ExternalYMProofSource
originalJointExistenceReceipt = ymProofSource jointExistence
  sourceRepository sourceGitCommit "Solution.lean"
  "YangMills.jointExistence"
  "Original Lean source target; mass gap and limit uniqueness excluded"
  "YMClayE1VariableCutoffCylinderLimitExact"

reviewCombinedReceipt : ExternalYMProofSource
reviewCombinedReceipt = ymProofSource reviewedCombinedAcceptance
  reviewRepository reviewGitCommit
  "submissions/openai-20261028/checks/CombinedAcceptance.lean"
  "YMReview.Acceptance.combined_acceptance"
  "One Wilson family, extracted table and final witness; selected scalar OS"
  "YMClayOriginalF19P0CommonOSSourceConvergence20261114"

reviewOPEReceipt : ExternalYMProofSource
reviewOPEReceipt = ymProofSource reviewedOPE
  reviewRepository reviewGitCommit
  "submissions/openai-20261028/checks/OPECheck.lean"
  "YMReview.OPE.constructed"
  "Separate OPE endpoint; not proved same as combined witness"
  "YangMillsStressWardCommonCoreGeneratorExact"

-- An upstream theorem is not an Agda proof, nor evidence that its choice of
-- Wilson group, gauge normalization, block map, test algebra, scaling sequence,
-- OS Hilbert space or stress tensor is literally the DASHI original object.
record CrossKernelPromotionBoundary : Set where
  constructor crossKernelBoundary
  field
    upstreamCommitteeChecksReported : Bool
    originalBytesPinnedHere : Bool
    localDASHILean432RebuildPaid : Bool
    localDASHILean428PortPaid : Bool
    nativeWorldBuilderIngestPaid : Bool
    sameWilsonFamilyAndBlockingPaid : Bool
    sameOriginalOsterwalderSchraderCarrierPaid : Bool
    sameStressWardHamiltonianPaid : Bool
    dashiE1ExistencePaid : Bool
    dashiD1CovarianceMassPaid : Bool
    dashiD2SpectralGapPaid : Bool
    dashiN1AndG1Paid : Bool
    clayMassGapPaid : Bool

pinnedOAIYMReceiptBoundary : CrossKernelPromotionBoundary
pinnedOAIYMReceiptBoundary = crossKernelBoundary
  false false false false false false false false false false false false false

-- The committee's recorded independent checks are documented separately;
-- this conservative local receipt does not construct any proof of them.
noLocalE1Promotion :
  CrossKernelPromotionBoundary.dashiE1ExistencePaid pinnedOAIYMReceiptBoundary ≡ false
noLocalE1Promotion = refl

noLocalGapPromotion :
  CrossKernelPromotionBoundary.clayMassGapPaid pinnedOAIYMReceiptBoundary ≡ false
noLocalGapPromotion = refl

upstreamReviewedDoesNotImportAgdaProof : Bool
upstreamReviewedDoesNotImportAgdaProof = false
