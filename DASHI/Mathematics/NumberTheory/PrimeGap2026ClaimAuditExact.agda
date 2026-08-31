module DASHI.Mathematics.NumberTheory.PrimeGap2026ClaimAuditExact where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

-- Source-bounded audit for the August 2026 reported large-prime-gap
-- improvement and a separately reported Lean formalization.
--
-- This does not transcribe the new proof and therefore does not assert the
-- record theorem inside Agda.  It establishes the trust/provenance interface
-- needed before such a transcription is promoted.

data ResultRole : Set where
  priorPublishedTheorem : ResultRole
  newInformalMathematicalArgument : ResultRole
  leanFormalization : ResultRole
  agdaFormalization : ResultRole
  humanCorrespondenceReview : ResultRole
  peerReviewedPublication : ResultRole

data VerificationStatus : Set where
  announced : VerificationStatus
  sourceRecovered : VerificationStatus
  kernelAcceptedExternally : VerificationStatus
  correspondenceChecked : VerificationStatus
  independentlyReviewed : VerificationStatus

record PrimeGapClaim : Set where
  field
    theoremRole : ResultRole
    status : VerificationStatus
    claimedGainLog3Factor : Set

-- A Lean kernel receipt is evidence about a Lean term, not definitionally an
-- Agda theorem and not by itself a proof that the formal statement matches the
-- intended informal theorem.
leanNotAgda : leanFormalization ≡ agdaFormalization -> ⊥
leanNotAgda ()

kernelAcceptanceNotCorrespondenceReview : kernelAcceptedExternally ≡ correspondenceChecked -> ⊥
kernelAcceptanceNotCorrespondenceReview ()

announcementNotIndependentReview : announced ≡ independentlyReviewed -> ⊥
announcementNotIndependentReview ()

newArgumentNotPriorTheorem : newInformalMathematicalArgument ≡ priorPublishedTheorem -> ⊥
newArgumentNotPriorTheorem ()

record ExternalLeanReturn : Set where
  field
    statementRecovered : Set
    kernelReceiptRecovered : Set
    dependencyAuditRecovered : Set

record CorrespondenceBridge : Set where
  field
    informalStatementRecovered : Set
    leanStatementRecovered : Set
    statementCorrespondence : Set

record AgdaPromotionGate : Set where
  field
    sourceProofRecovered : Set
    exactTheoremStatementRecovered : Set
    externalLeanReturn : ExternalLeanReturn
    correspondenceBridge : CorrespondenceBridge
    agdaProofOrTrustedImport : Set

-- The gate deliberately requires both mathematical-source recovery and
-- statement correspondence.  A successful external Lean build alone cannot
-- inhabit it.
