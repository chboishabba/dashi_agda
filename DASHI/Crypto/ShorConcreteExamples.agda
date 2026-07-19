module DASHI.Crypto.ShorConcreteExamples where

open import DASHI.Core.Prelude
open import DASHI.Foundations.Base369Nat using (nonZero)
open import DASHI.Crypto.RSAArithmeticCore
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Crypto.ShorFactoring
open import DASHI.Crypto.RSAShorVulnerabilityBridge

------------------------------------------------------------------------
-- Exact finite examples.
------------------------------------------------------------------------

shor15Problem : ShorFactoringProblem 15
shor15Problem = record
  { base = 2
  ; order = 4
  ; split = shorSplit15
  }

shor15ExtractsThree :
  proj₁ (classicalShorFactor shor15Problem) ≡ 3
shor15ExtractsThree = refl

rsa15PublicState : RSAPublicState
rsa15PublicState =
  mkRSAPublicState
    15
    nonZero
    3
    false
    refl

rsa15Vulnerability : RSAShorVulnerability rsa15PublicState
rsa15Vulnerability = record
  { factoringProblem = shor15Problem
  }

rsa15ShorExtractsThree :
  factor (exposeRSAFactor rsa15Vulnerability) ≡ 3
rsa15ShorExtractsThree = refl

shor21Problem : ShorFactoringProblem 21
shor21Problem = record
  { base = 2
  ; order = 6
  ; split = shorSplit21
  }

shor21ExtractsSeven :
  proj₁ (classicalShorFactor shor21Problem) ≡ 7
shor21ExtractsSeven = refl
