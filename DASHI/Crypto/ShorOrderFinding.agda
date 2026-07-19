module DASHI.Crypto.ShorOrderFinding where

open import DASHI.Core.Prelude
open import DASHI.Crypto.RSAArithmeticCore using (powMod)
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Algebra.Quantum.GeneralShor

------------------------------------------------------------------------
-- Modular exponentiation as a cyclic hidden-period problem.
------------------------------------------------------------------------

record ModularOrderProblem (N a r : Nat) : Set₁ where
  field
    exactOrder : ExactOrderCertificate N a r

    periodTransport :
      ∀ x →
      powMod a (x + r) N
        {{modulusNonZero (periodCertificate exactOrder)}}
      ≡
      powMod a x N
        {{modulusNonZero (periodCertificate exactOrder)}}

    exactTransport :
      ∀ k →
      Positive k →
      k < r →
      ¬
        (∀ x →
          powMod a (x + k) N
            {{modulusNonZero (periodCertificate exactOrder)}}
          ≡
          powMod a x N
            {{modulusNonZero (periodCertificate exactOrder)}})

open ModularOrderProblem public

asHiddenPeriodProblem :
  ∀ {N a r} →
  ModularOrderProblem N a r →
  HiddenPeriodProblem
asHiddenPeriodProblem {N} {a} {r} P = record
  { Value = Nat
  ; oracle = λ x →
      powMod a x N
        {{modulusNonZero (periodCertificate (exactOrder P))}}
  ; period = r
  ; periodPositive =
      positivePeriod (periodCertificate (exactOrder P))
  ; periodic = periodTransport P
  ; exactPeriod = exactTransport P
  }

record CertifiedOrderFindingRun
    {N a r : Nat}
    (P : ModularOrderProblem N a r) : Set₁ where
  field
    machine : ShorPeriodFindingMachine (asHiddenPeriodProblem P)
    successEvidence : ShorSuccessEvidence machine

open CertifiedOrderFindingRun public

orderFindingRecoversExactOrder :
  ∀ {N a r} →
  (P : ModularOrderProblem N a r) →
  (R : CertifiedOrderFindingRun P) →
  recoverPeriod
    (machine R)
    (execute (machine R) (seed (successEvidence R)))
  ≡ r
orderFindingRecoversExactOrder P R =
  recoveredPeriodIsExact (machine R) (successEvidence R)
