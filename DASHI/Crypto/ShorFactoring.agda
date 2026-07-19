module DASHI.Crypto.ShorFactoring where

open import DASHI.Core.Prelude
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Crypto.ShorOrderFinding

------------------------------------------------------------------------
-- General Shor factoring programme.
------------------------------------------------------------------------

record ShorFactoringProblem (N : Nat) : Set₁ where
  field
    base : Nat
    order : Nat
    split : CertifiedShorSplit N base order

open ShorFactoringProblem public

classicalShorFactor :
  ∀ {N} →
  ShorFactoringProblem N →
  Σ Nat (λ d → FactorCertificate N d)
classicalShorFactor P = extractCertifiedFactor (split P)

record QuantumShorFactoringRun
    {N : Nat}
    (P : ShorFactoringProblem N) : Set₁ where
  field
    modularOrderProblem :
      ModularOrderProblem N (base P) (order P)

    orderFindingRun :
      CertifiedOrderFindingRun modularOrderProblem

open QuantumShorFactoringRun public

quantumRecoveredOrder :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  QuantumShorFactoringRun P →
  Nat
quantumRecoveredOrder P R =
  recoverPeriod
    (machine (orderFindingRun R))
    (execute
      (machine (orderFindingRun R))
      (seed (successEvidence (orderFindingRun R))))

quantumRecoveredOrderIsSplitOrder :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  (R : QuantumShorFactoringRun P) →
  quantumRecoveredOrder P R ≡ order P
quantumRecoveredOrderIsSplitOrder P R =
  orderFindingRecoversExactOrder
    (modularOrderProblem R)
    (orderFindingRun R)

quantumShorFactor :
  ∀ {N} →
  (P : ShorFactoringProblem N) →
  QuantumShorFactoringRun P →
  Σ Nat (λ d → FactorCertificate N d)
quantumShorFactor P R = classicalShorFactor P
