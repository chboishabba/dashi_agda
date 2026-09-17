module DASHI.Crypto.ShorQuantumRunFactorTransportExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Crypto.ShorFactoring

------------------------------------------------------------------------
-- Quantum-run-dependent factor extraction.
--
-- `ShorFactoring` already proves that the certified quantum execution recovers
-- exactly the order stored in the factoring problem.  The missing seam was
-- that factor extraction still consumed `split P` at the declared order and
-- therefore did not depend on the recovered order at all.
--
-- We pay only that equality transport here: move the existing certified split
-- along the proved equality
--
--   quantumRecoveredOrder P R ≡ order P
--
-- so the split is indexed by the order actually returned by the quantum run.
-- No new arithmetic, probability, circuit semantics, or factor authority is
-- introduced.
------------------------------------------------------------------------

quantumRecoveredOrderSplit :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  (R : QuantumShorFactoringRun P) →
  CertifiedShorSplit
    N
    (base P)
    (quantumRecoveredOrder P R)
quantumRecoveredOrderSplit P R =
  subst
    (λ r → CertifiedShorSplit _ (base P) r)
    (sym (quantumRecoveredOrderIsSplitOrder P R))
    (split P)

quantumShorFactorFromRecoveredOrder :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  (R : QuantumShorFactoringRun P) →
  Σ Nat (λ d → FactorCertificate N d)
quantumShorFactorFromRecoveredOrder P R =
  extractCertifiedFactor (quantumRecoveredOrderSplit P R)

quantumRecoveredOrderFactorAgreesWithClassical :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  (R : QuantumShorFactoringRun P) →
  quantumShorFactorFromRecoveredOrder P R ≡ classicalShorFactor P
quantumRecoveredOrderFactorAgreesWithClassical P R
  with quantumRecoveredOrderIsSplitOrder P R
... | refl = refl
