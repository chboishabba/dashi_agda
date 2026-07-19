module DASHI.Crypto.RSAShorVulnerabilityBridge where

open import DASHI.Core.Prelude
open import DASHI.Crypto.RSAArithmeticCore
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Crypto.ShorFactoring

------------------------------------------------------------------------
-- RSA modulus -> Shor factoring bridge.
------------------------------------------------------------------------

record RSAShorVulnerability
    (publicState : RSAPublicState) : Set₁ where
  field
    factoringProblem :
      ShorFactoringProblem (publicModulus publicState)

open RSAShorVulnerability public

rsaShorFactor :
  ∀ {publicState} →
  RSAShorVulnerability publicState →
  Σ Nat (λ d → FactorCertificate (publicModulus publicState) d)
rsaShorFactor V = classicalShorFactor (factoringProblem V)

record RSAQuantumShorBreak
    (publicState : RSAPublicState)
    (V : RSAShorVulnerability publicState) : Set₁ where
  field
    quantumRun :
      QuantumShorFactoringRun (factoringProblem V)

open RSAQuantumShorBreak public

rsaQuantumShorFactor :
  ∀ {publicState} →
  (V : RSAShorVulnerability publicState) →
  RSAQuantumShorBreak publicState V →
  Σ Nat (λ d → FactorCertificate (publicModulus publicState) d)
rsaQuantumShorFactor V B =
  quantumShorFactor (factoringProblem V) (quantumRun B)

record RSAFactorizationExposure
    (publicState : RSAPublicState) : Set₁ where
  field
    factor : Nat
    certificate :
      FactorCertificate (publicModulus publicState) factor

open RSAFactorizationExposure public

exposeRSAFactor :
  ∀ {publicState} →
  RSAShorVulnerability publicState →
  RSAFactorizationExposure publicState
exposeRSAFactor V with rsaShorFactor V
... | d , C = record
  { factor = d
  ; certificate = C
  }
