module DASHI.Crypto.ShorFourierOrderCandidateVerificationRegression where

open import DASHI.Core.Prelude

import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorFourierOrderCandidateVerificationExact as Verify

------------------------------------------------------------------------
-- RED regression: an independently produced Fourier/order candidate carrying
-- a genuine ExactOrderCertificate must be forced to the problem's exact order.
------------------------------------------------------------------------

candidateEqualsExactOrder :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (C : Verify.CertifiedFourierOrderCandidate P) →
  Verify.candidateOrder C ≡ r
candidateEqualsExactOrder = Verify.certifiedFourierCandidateIsExactOrder

candidateRecoveryIsExact :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (C : Verify.CertifiedFourierOrderCandidate P) →
  Verify.recoverCertifiedFourierOrder C ≡ r
candidateRecoveryIsExact = Verify.recoverCertifiedFourierOrderIsExact
