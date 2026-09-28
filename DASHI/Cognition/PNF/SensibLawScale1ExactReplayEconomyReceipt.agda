module DASHI.Cognition.PNF.SensibLawScale1ExactReplayEconomyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Literal SCALE-1 exact-replay measurement cut, 2026-09-28.
--
-- These are runtime measurements only.  The replay reused every parser job,
-- therefore parser wall for this run is not a fresh parser-performance
-- measurement and cannot be combined with the review wall to manufacture a
-- parser-dominance certification.
------------------------------------------------------------------------

record ExactReplayEconomyReceipt : Set where
  constructor exact-replay-economy-receipt
  field
    sourceRevisionRef : String
    parserRunRef : String

    parserNewJobs : Nat
    parserReusedJobs : Nat
    semanticEligibleRegions : Nat
    parserNewJobsZero : parserNewJobs ≡ 0
    allParserJobsReused : parserReusedJobs ≡ semanticEligibleRegions

    candidatePersistenceReused : Bool
    candidatePersistenceReusedIsTrue :
      candidatePersistenceReused ≡ true

    candidateCommitCount : Nat
    candidateCommitCountZero : candidateCommitCount ≡ 0

    candidatePostcommitReopenQueries : Nat
    candidatePostcommitReopenQueriesZero :
      candidatePostcommitReopenQueries ≡ 0

    l2Reused : Bool
    l2ReusedIsTrue : l2Reused ≡ true

    autoReused : Bool
    autoReusedIsTrue : autoReused ≡ true

    unattemptedSemanticRegions : Nat
    unattemptedSemanticRegionsZero :
      unattemptedSemanticRegions ≡ 0

    sourceRegionLossCount : Nat
    sourceRegionLossCountZero :
      sourceRegionLossCount ≡ 0

    candidatePersistNs : Nat
    l2ReconciliationNs : Nat
    autoEventNs : Nat
    reviewProjectionNs : Nat
    finalizeInternalTotalNs : Nat
    totalNs : Nat

    parserMeasuredThisRun : Bool
    parserMeasuredThisRunIsFalse :
      parserMeasuredThisRun ≡ false

    semanticAuthorityCreated : Bool
    semanticAuthorityCreatedIsFalse :
      semanticAuthorityCreated ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open ExactReplayEconomyReceipt public

gwbExactReplay20260928 : ExactReplayEconomyReceipt
gwbExactReplay20260928 =
  exact-replay-economy-receipt
    "source-revision:sha256:8dd2afe20c7cfb36bc1372f764b7683962e6acdfac6fe0bfa47554812d4eab00"
    "parser-run:sha256:56ea4c0a05c3beb97f05dfe447570c7d753f15d8b8bf76cb86145ca41f8f2d63"
    0
    6678
    6678
    refl
    refl
    true refl
    0 refl
    0 refl
    true refl
    true refl
    0 refl
    0 refl
    97843574
    59155701
    68139253
    235185790641
    247674856598
    260410943371
    false refl
    false refl
    false refl
    false refl

data ExactReplayCertifiesFreshParserDominance : Set where
data ReplayEconomyReceiptPromotesSemanticTruth : Set where

exactReplayCannotCertifyFreshParserDominance :
  ExactReplayCertifiesFreshParserDominance → ⊥
exactReplayCannotCertifyFreshParserDominance ()

replayEconomyReceiptDoesNotPromoteSemanticTruth :
  ReplayEconomyReceiptPromotesSemanticTruth → ⊥
replayEconomyReceiptDoesNotPromoteSemanticTruth ()

exactReplayHasNoFreshParserMeasurement :
  parserMeasuredThisRun gwbExactReplay20260928 ≡ false
exactReplayHasNoFreshParserMeasurement = refl

exactReplayCandidatePathUsesNoCommitBarrier :
  candidateCommitCount gwbExactReplay20260928 ≡ 0
exactReplayCandidatePathUsesNoCommitBarrier = refl

exactReplayCandidatePathUsesNoReopenQuery :
  candidatePostcommitReopenQueries gwbExactReplay20260928 ≡ 0
exactReplayCandidatePathUsesNoReopenQuery = refl
