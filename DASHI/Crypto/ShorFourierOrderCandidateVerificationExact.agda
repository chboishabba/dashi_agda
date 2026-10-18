module DASHI.Crypto.ShorFourierOrderCandidateVerificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import Data.Nat.Properties as NatP
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)

import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT

------------------------------------------------------------------------
-- Q3 FOURIER-CANDIDATE VERIFICATION
--
-- Continued-fraction/rational-reconstruction code is a producer of candidate
-- periods, not an authority for their correctness.  The repository already
-- owns `ExactOrderCertificate`: a positive period plus exclusion of every
-- smaller positive period.  Two such certificates for the same (N,a) cannot
-- disagree.  This gives the Shor sampling lane the same producer/verifier split
-- used elsewhere in DASHI.
--
-- A Fourier sample may therefore arrive with a candidate order from any
-- explicitly attributed extractor.  Once an ExactOrderCertificate for that
-- candidate is attached, kernel-level arithmetic forces it to be the exact
-- order stored by the modular-order problem.
------------------------------------------------------------------------

exactOrderCertificateUnique :
  ∀ {N a left right} →
  Factor.ExactOrderCertificate N a left →
  Factor.ExactOrderCertificate N a right →
  left ≡ right
exactOrderCertificateUnique {left = left} {right = right} leftCert rightCert
  with NatP.<-cmp left right
... | tri≈ _ left≡right _ = left≡right
... | tri< left<right _ _ =
  ⊥-elim
    ((Factor.earlierNonperiod rightCert
        left
        (Factor.positivePeriod (Factor.periodCertificate leftCert))
        left<right)
      (Factor.periodLaw (Factor.periodCertificate leftCert)))
... | tri> _ _ right<left =
  ⊥-elim
    ((Factor.earlierNonperiod leftCert
        right
        (Factor.positivePeriod (Factor.periodCertificate rightCert))
        right<left)
      (Factor.periodLaw (Factor.periodCertificate rightCert)))

record CertifiedFourierOrderCandidate
    {N a r : Nat}
    (P : Order.ModularOrderProblem N a r) : Set₁ where
  constructor certifiedFourierOrderCandidate
  field
    rawFourierSample : QFT.FourierSample
    candidateOrder : Nat
    candidateCertificate :
      Factor.ExactOrderCertificate N a candidateOrder
    extractorReference : String

open CertifiedFourierOrderCandidate public

certifiedFourierCandidateIsExactOrder :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (C : CertifiedFourierOrderCandidate P) →
  candidateOrder C ≡ r
certifiedFourierCandidateIsExactOrder P C =
  exactOrderCertificateUnique
    (candidateCertificate C)
    (Order.exactOrder P)

recoverCertifiedFourierOrder :
  ∀ {N a r}
    {P : Order.ModularOrderProblem N a r} →
  CertifiedFourierOrderCandidate P → Nat
recoverCertifiedFourierOrder = candidateOrder

recoverCertifiedFourierOrderIsExact :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (C : CertifiedFourierOrderCandidate P) →
  recoverCertifiedFourierOrder C ≡ r
recoverCertifiedFourierOrderIsExact =
  certifiedFourierCandidateIsExactOrder

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ShorFourierCandidateVerificationBoundary : Set where
  constructor shorFourierCandidateVerificationBoundary
  field
    fourierSampleRetained : Bool
    candidateExtractorAttributed : Bool
    exactOrderCandidateKernelVerified : Bool
    exactOrderUniquenessProved : Bool
    continuedFractionExtractorImplementedHere : Bool
    samplingDistributionProvedHere : Bool
    candidateCertificateMayBeOmitted : Bool

canonicalShorFourierCandidateVerificationBoundary :
  ShorFourierCandidateVerificationBoundary
canonicalShorFourierCandidateVerificationBoundary =
  shorFourierCandidateVerificationBoundary
    true true true true false false false
