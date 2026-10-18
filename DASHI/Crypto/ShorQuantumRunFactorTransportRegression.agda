module DASHI.Crypto.ShorQuantumRunFactorTransportRegression where

open import DASHI.Crypto.ShorQuantumRunFactorTransportExact

------------------------------------------------------------------------
-- Regression surface: the quantum factoring result must flow through the
-- recovered order supplied by the certified quantum run, rather than ignore
-- that run and reuse the pre-existing classical split directly.
------------------------------------------------------------------------

open import DASHI.Crypto.ShorFactoring

quantumRunFactorRegression :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  (R : QuantumShorFactoringRun P) →
  Σ Nat (λ d → FactorCertificate N d)
quantumRunFactorRegression = quantumShorFactorFromRecoveredOrder
