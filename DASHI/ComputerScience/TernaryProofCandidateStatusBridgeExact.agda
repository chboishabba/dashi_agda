module DASHI.ComputerScience.TernaryProofCandidateStatusBridgeExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Foundations.TernaryElementarySearchCertificate as Search
import DASHI.ComputerScience.TernaryProofSearchDecisionDebtBridgeExact as GlobalSearch

------------------------------------------------------------------------
-- EXISTING PROOF-CANDIDATE STATUS -> TERNARY LOCAL DECISION
--
-- This is candidate-local adjudication, not global theorem/search status:
--
--   scoutOnly / symbolicCandidate -> zer
--   certified                     -> pos
--   refuted                       -> neg
--
-- In particular, candidate refutation and complete finite-search exhaustion
-- are two distinct producers of a negative trit and remain provenance-typed.
------------------------------------------------------------------------

candidateStatusTrit : Search.CandidateStatus → Trit
candidateStatusTrit Search.scoutOnly = zer
candidateStatusTrit Search.symbolicCandidate = zer
candidateStatusTrit Search.certified = pos
candidateStatusTrit Search.refuted = neg

candidateDecision : Search.SearchCandidate → Trit
candidateDecision candidate = candidateStatusTrit (Search.status candidate)

-- The repository's known diagonal unit candidate is still symbolic until its
-- analytic side conditions are paid, so it remains unresolved.
diagonalUnitCandidateStillUnresolved :
  (witness : Search.Var) →
  candidateDecision (Search.diagonalUnitSearchCandidate witness) ≡ zer
diagonalUnitCandidateStillUnresolved witness = refl

------------------------------------------------------------------------
-- A CertifiedSearchCandidate has an inhabited exact rewrite trace and a receipt
-- that its underlying candidate status is certified.  That is enough to
-- transport the candidate-local trit to positive.
------------------------------------------------------------------------

certifiedCandidateIsPositive :
  (A : Search.SideConditionAuthority) →
  (candidate : Search.CertifiedSearchCandidate A) →
  candidateDecision (Search.candidateData candidate) ≡ pos
certifiedCandidateIsPositive A candidate
  rewrite Search.candidateStatusIsCertified candidate = refl

------------------------------------------------------------------------
-- Negative provenance must remain explicit.
------------------------------------------------------------------------

data CandidateNegativeReason : Set where
  individualCandidateRefuted : CandidateNegativeReason
  completeDeclaredDomainExhausted : CandidateNegativeReason

record NegativeProofSearchReceipt : Set where
  constructor negativeProofSearchReceipt
  field
    decision : Trit
    reason : CandidateNegativeReason
    decisionIsNegative : decision ≡ neg

open NegativeProofSearchReceipt public

candidateRefutationNegativeReceipt : NegativeProofSearchReceipt
candidateRefutationNegativeReceipt =
  negativeProofSearchReceipt neg individualCandidateRefuted refl

finiteDomainExhaustionNegativeReceipt : NegativeProofSearchReceipt
finiteDomainExhaustionNegativeReceipt =
  negativeProofSearchReceipt neg completeDeclaredDomainExhausted refl

-- Same ternary value does not identify the reason/provenance fibre.
data EqualNegativeTritImpliesEqualNegativeReason : Set where

equalNegativeDoesNotIdentifyReason :
  EqualNegativeTritImpliesEqualNegativeReason → ⊥
equalNegativeDoesNotIdentifyReason ()

-- Candidate-level neg does not by itself license the global complete-search neg.
data RefutedCandidateMeansCompleteSearchExhausted : Set where

refutedCandidateDoesNotExhaustSearch :
  RefutedCandidateMeansCompleteSearchExhausted → ⊥
refutedCandidateDoesNotExhaustSearch ()

-- Nor does a complete bounded search refute the theorem outside its declared
-- admissible candidate domain; the global bridge already keeps that firewall.
data CompleteBoundedSearchMeansTheoremFalse : Set where

completeBoundedSearchDoesNotMeanTheoremFalse :
  CompleteBoundedSearchMeansTheoremFalse → ⊥
completeBoundedSearchDoesNotMeanTheoremFalse ()

record TernaryProofCandidateStatusBoundary : Set where
  constructor ternaryProofCandidateStatusBoundary
  field
    symbolicCandidateMapsUnresolved : Bool
    certifiedCandidateMapsPositive : Bool
    refutedCandidateMapsNegative : Bool
    candidateNegativeDistinctFromGlobalExhaustion : Bool
    sameNegativeTritIdentifiesReason : Bool
    refutedCandidateExhaustsGlobalSearch : Bool

canonicalTernaryProofCandidateStatusBoundary :
  TernaryProofCandidateStatusBoundary
canonicalTernaryProofCandidateStatusBoundary =
  ternaryProofCandidateStatusBoundary
    true true true true false false
