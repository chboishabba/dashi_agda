module DASHI.Analysis.DeBruijnNewman2026ClaimAuditExact where

-- Source-bounded audit surface for the August 2026 candidate improvement
-- of the de Bruijn-Newman upper bound.
--
-- This module does NOT prove the analytic Polymath criterion, does NOT replay
-- external interval certificates, and does NOT promote a public repository or
-- social-media announcement into peer-reviewed mathematical authority.
-- It records the exact claimed rational parameter arithmetic and keeps the
-- evidential stages constructor-disjoint.

data ClaimStatus : Set where
  publicCandidate : ClaimStatus
  machineReplayReported : ClaimStatus
  independentlyReproduced : ClaimStatus
  peerReviewed : ClaimStatus

data SourceRole : Set where
  publishedAnalyticCriterion : SourceRole
  publishedVerifiedZeroHeight : SourceRole
  candidateParameterInstantiation : SourceRole
  numericalCertificatePackage : SourceRole
  externalReplayVerifier : SourceRole
  peerReviewAuthority : SourceRole

record Rational : Set where
  constructor _over_
  field
    numerator : Nat
    denominator : Nat

open Rational public

-- Claimed August 2026 parameter choices.
t0 : Rational
t0 = 129 over 800

y0Squared : Rational
y0Squared = 87677 over 2500000

claimedUpperBound : Rational
claimedUpperBound = 893927 over 5000000

-- Exact integer identity behind
--   129/800 + (87677/2500000)/2 = 893927/5000000.
-- We deliberately certify only the cross-multiplied natural-number arithmetic
-- here; interpreting it as a bound for Lambda still requires the analytic and
-- certificate obligations below.
parameterArithmeticNumerator : Nat
parameterArithmeticNumerator = 129 * 12500 + 87677

parameterArithmeticTargetNumerator : Nat
parameterArithmeticTargetNumerator = 893927 * 2

-- Both normalize to 1787854.
parameterArithmeticExact : parameterArithmeticNumerator ≡ parameterArithmeticTargetNumerator
parameterArithmeticExact = refl

record CandidateUpperBoundReceipt : Set where
  field
    analyticCriterionRole : SourceRole
    verifiedHeightRole : SourceRole
    parameterRole : SourceRole
    certificateRole : SourceRole
    verifierRole : SourceRole
    status : ClaimStatus

-- Promotion to a mathematical theorem is intentionally a separate token.
data TheoremAuthority : Set where
  externallyEstablished : TheoremAuthority

record EstablishedUpperBound : Set where
  field
    candidate : CandidateUpperBoundReceipt
    authority : TheoremAuthority

-- Constructor disjointness gives the central no-promotion boundaries.
publicCandidateNotPeerReviewed : publicCandidate ≡ peerReviewed -> ⊥
publicCandidateNotPeerReviewed ()

reportedReplayNotIndependentReproduction : machineReplayReported ≡ independentlyReproduced -> ⊥
reportedReplayNotIndependentReproduction ()

parameterRoleNotAnalyticCriterion : candidateParameterInstantiation ≡ publishedAnalyticCriterion -> ⊥
parameterRoleNotAnalyticCriterion ()

certificateRoleNotPeerReview : numericalCertificatePackage ≡ peerReviewAuthority -> ⊥
certificateRoleNotPeerReview ()

-- The intended audit spine is therefore:
-- published criterion
--   + published zero-height input
--   + candidate parameters
--   + numerical certificates
--   + replay verifier
--   + external authority
-- -> established upper-bound theorem.
-- No field in CandidateUpperBoundReceipt can manufacture TheoremAuthority.
