module DASHI.Core.HumanReviewCore where

------------------------------------------------------------------------
-- GENERIC HUMAN REVIEW CORE
--
-- Domain-neutral carrier extracted from SensibLaw REAL-MATTER review work.
--
-- A review receipt records who reviewed which item under which observation.
-- An exact-item binding ties that review to the concrete source manifestation,
-- candidate batch/factor, and declared consumer. Neither object creates truth,
-- applicability, causal identification, legal authority, or domain authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record GenericHumanReviewReceipt : Set where
  constructor generic-human-review-receipt
  field
    reviewReceiptRef : String
    reviewItemRef : String
    reviewerRef : String
    observationRef : String

open GenericHumanReviewReceipt public

record ExactReviewItemBinding : Set where
  constructor exact-review-item-binding
  field
    sourceManifestationRef : String
    candidatePnfBatchRef : String
    candidateFactorRef : String
    consumerRef : String
    acceptedOrQualified : Bool
    acceptedOrQualifiedIsTrue : acceptedOrQualified ≡ true

open ExactReviewItemBinding public

record HumanReviewCoreBoundary : Set where
  constructor human-review-core-boundary
  field
    exactSourceManifestationRetained : Bool
    exactCandidateRetained : Bool
    declaredConsumerRetained : Bool
    acceptedOrQualifiedRequired : Bool
    reviewCreatesClaimTruth : Bool
    reviewCreatesApplicability : Bool
    reviewCreatesCausalIdentification : Bool
    reviewCreatesDomainAuthority : Bool

canonicalHumanReviewCoreBoundary : HumanReviewCoreBoundary
canonicalHumanReviewCoreBoundary =
  human-review-core-boundary
    true true true true false false false false
