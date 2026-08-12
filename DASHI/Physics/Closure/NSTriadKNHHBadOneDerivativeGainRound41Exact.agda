module DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeGainRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: P. K. Mitter.
-- Title: "The Exact Renormalization Group".
-- Persistent identifier: 10.48550/arXiv.math-ph/0505008.
--
-- Authors: Wojciech Dybalski; Alexander Stottmeister; Yoh Tanimoto.
-- Title: "The Bałaban variational problem in the non-linear sigma model".
-- Persistent identifier: 10.48550/arXiv.2403.09800.
--
-- DASHI CONTRIBUTION
--
-- Round 36 proved the signed scale valuation saying that one derivative on
-- exactly one side of a parabolic inverse can create the inverse shell power
-- required by HH-bad, whereas two derivative-bearing sides cannot.  This file
-- upgrades that valuation to an exact rational magnitude calculation on the
-- repository's literal dyadic scale.
--
-- Write lambda_q = 2^q and mu_q = 2^-q, with mu_q lambda_q = 1.  A schematic
-- one-derivative Schur magnitude has the exact scalar form
--
--   (L lambda_q) (nu^-1 mu_q^2) R
--     = L nu^-1 R mu_q.
--
-- Hence multiplying by lambda_q removes precisely one inverse shell factor.
-- In contrast the two-derivative form is
--
--   (L lambda_q) (nu^-1 mu_q^2) (R lambda_q)
--     = L nu^-1 R,
--
-- which is shell-scale-free.  This is a stronger falsification gate than a
-- dimensional slogan: once the literal bad gain is identified with one of
-- these factorizations, Agda checks the exact dyadic cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp

rawOneDerivativeSchurMagnitude : ℚ → ℚ → ℚ → Nat → ℚ
rawOneDerivativeSchurMagnitude left viscosityInverse right shell =
  (left * Sharp.dyadicScale shell)
  * (viscosityInverse
      * Sharp.inverseDyadicScale shell
      * Sharp.inverseDyadicScale shell)
  * right

normalizedOneDerivativeSchurMagnitude : ℚ → ℚ → ℚ → Nat → ℚ
normalizedOneDerivativeSchurMagnitude left viscosityInverse right shell =
  left * viscosityInverse * right * Sharp.inverseDyadicScale shell

rawTwoDerivativeSchurMagnitude : ℚ → ℚ → ℚ → Nat → ℚ
rawTwoDerivativeSchurMagnitude left viscosityInverse right shell =
  (left * Sharp.dyadicScale shell)
  * (viscosityInverse
      * Sharp.inverseDyadicScale shell
      * Sharp.inverseDyadicScale shell)
  * (right * Sharp.dyadicScale shell)

normalizedTwoDerivativeSchurMagnitude : ℚ → ℚ → ℚ
normalizedTwoDerivativeSchurMagnitude left viscosityInverse right =
  left * viscosityInverse * right

oneDerivativeSchurNormalizesToInverseShell :
  ∀ left viscosityInverse right shell →
  rawOneDerivativeSchurMagnitude left viscosityInverse right shell
  ≡ normalizedOneDerivativeSchurMagnitude
      left viscosityInverse right shell
oneDerivativeSchurNormalizesToInverseShell left viscosityInverse right shell =
  let
    lambda = Sharp.dyadicScale shell
    mu = Sharp.inverseDyadicScale shell

    regroup :
      (left * lambda) * (viscosityInverse * mu * mu) * right
      ≡ left * viscosityInverse * right * (mu * lambda) * mu
    regroup = solve
      (left ∷ viscosityInverse ∷ right ∷ lambda ∷ mu ∷ [])

    cancel :
      left * viscosityInverse * right * (mu * lambda) * mu
      ≡ left * viscosityInverse * right * mu
    cancel = cong
      (λ reciprocal →
        left * viscosityInverse * right * reciprocal * mu)
      (Sharp.inverseDyadicReciprocal shell)
  in
  trans regroup
    (trans cancel
      (solve
        (left ∷ viscosityInverse ∷ right ∷ mu ∷ [])))

oneDerivativeDensityTimesShellIsScaleFree :
  ∀ left viscosityInverse right shell →
  rawOneDerivativeSchurMagnitude left viscosityInverse right shell
    * Sharp.dyadicScale shell
  ≡ normalizedTwoDerivativeSchurMagnitude left viscosityInverse right
oneDerivativeDensityTimesShellIsScaleFree
    left viscosityInverse right shell =
  let
    mu = Sharp.inverseDyadicScale shell
    lambda = Sharp.dyadicScale shell

    first :
      rawOneDerivativeSchurMagnitude left viscosityInverse right shell
        * lambda
      ≡ left * viscosityInverse * right * mu * lambda
    first = cong (_* lambda)
      (oneDerivativeSchurNormalizesToInverseShell
        left viscosityInverse right shell)

    second :
      left * viscosityInverse * right * mu * lambda
      ≡ left * viscosityInverse * right * (mu * lambda)
    second = solve
      (left ∷ viscosityInverse ∷ right ∷ mu ∷ lambda ∷ [])

    third :
      left * viscosityInverse * right * (mu * lambda)
      ≡ left * viscosityInverse * right
    third = cong
      (left * viscosityInverse * right *_)
      (Sharp.inverseDyadicReciprocal shell)
  in
  trans first (trans second third)

twoDerivativeSchurNormalizesToScaleFree :
  ∀ left viscosityInverse right shell →
  rawTwoDerivativeSchurMagnitude left viscosityInverse right shell
  ≡ normalizedTwoDerivativeSchurMagnitude left viscosityInverse right
twoDerivativeSchurNormalizesToScaleFree left viscosityInverse right shell =
  let
    lambda = Sharp.dyadicScale shell
    mu = Sharp.inverseDyadicScale shell

    regroup :
      (left * lambda)
        * (viscosityInverse * mu * mu)
        * (right * lambda)
      ≡ left * viscosityInverse * right
          * (mu * lambda) * (mu * lambda)
    regroup = solve
      (left ∷ viscosityInverse ∷ right ∷ lambda ∷ mu ∷ [])
  in
  trans regroup
    (trans
      (cong
        (λ reciprocal →
          left * viscosityInverse * right * reciprocal * reciprocal)
        (Sharp.inverseDyadicReciprocal shell))
      (solve (left ∷ viscosityInverse ∷ right ∷ [])))

record PhysicalHHBadOneDerivativeFactorization : Set where
  field
    leftCoefficient viscosityInverse rightCoefficient : ℚ
    shell : Nat
    physicalGainDensity : ℚ
    sameObjectFactorization :
      physicalGainDensity
      ≡ rawOneDerivativeSchurMagnitude
          leftCoefficient viscosityInverse rightCoefficient shell

open PhysicalHHBadOneDerivativeFactorization public

physicalOneDerivativeFactorizationExposesInverseShell :
  (factorization : PhysicalHHBadOneDerivativeFactorization) →
  physicalGainDensity factorization
  ≡ normalizedOneDerivativeSchurMagnitude
      (leftCoefficient factorization)
      (viscosityInverse factorization)
      (rightCoefficient factorization)
      (shell factorization)
physicalOneDerivativeFactorizationExposesInverseShell factorization =
  trans
    (sameObjectFactorization factorization)
    (oneDerivativeSchurNormalizesToInverseShell
      (leftCoefficient factorization)
      (viscosityInverse factorization)
      (rightCoefficient factorization)
      (shell factorization))

record PhysicalHHBadTwoDerivativeFactorization : Set where
  field
    leftCoefficient viscosityInverse rightCoefficient : ℚ
    shell : Nat
    physicalGainDensity : ℚ
    sameObjectFactorization :
      physicalGainDensity
      ≡ rawTwoDerivativeSchurMagnitude
          leftCoefficient viscosityInverse rightCoefficient shell

open PhysicalHHBadTwoDerivativeFactorization public

physicalTwoDerivativeFactorizationIsScaleFree :
  (factorization : PhysicalHHBadTwoDerivativeFactorization) →
  physicalGainDensity factorization
  ≡ normalizedTwoDerivativeSchurMagnitude
      (leftCoefficient factorization)
      (viscosityInverse factorization)
      (rightCoefficient factorization)
physicalTwoDerivativeFactorizationIsScaleFree factorization =
  trans
    (sameObjectFactorization factorization)
    (twoDerivativeSchurNormalizesToScaleFree
      (leftCoefficient factorization)
      (viscosityInverse factorization)
      (rightCoefficient factorization)
      (shell factorization))

hhBadOneDerivativeMagnitudeFactorizationClosed : Bool
hhBadOneDerivativeMagnitudeFactorizationClosed = true

twoDerivativeMagnitudeScaleFreeNoGoClosed : Bool
twoDerivativeMagnitudeScaleFreeNoGoClosed = true

physicalHHBadOneDerivativeFactorizationConstructed : Bool
physicalHHBadOneDerivativeFactorizationConstructed = false

hhBadOneDerivativeMagnitudeFactorizationClosedIsTrue :
  hhBadOneDerivativeMagnitudeFactorizationClosed ≡ true
hhBadOneDerivativeMagnitudeFactorizationClosedIsTrue = refl

twoDerivativeMagnitudeScaleFreeNoGoClosedIsTrue :
  twoDerivativeMagnitudeScaleFreeNoGoClosed ≡ true
twoDerivativeMagnitudeScaleFreeNoGoClosedIsTrue = refl
