module DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeFactorizationRound44Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- The remaining HH-bad target was phrased as a factorization
--
--   g_q = C_q 2^{-q}
--
-- followed by a shell-uniform bound on C_q.  The factorization itself does
-- not need to remain an analytic obligation.  For the literal Round-39 density
-- define, on the same certificate,
--
--   C_q := g_q 2^q.
--
-- The exact dyadic reciprocal law proves constructively
--
--   C_q 2^{-q} = g_q.
--
-- Hence the only genuinely analytic HH-bad scalar obligation is now the
-- scale-free coefficient bound C_q <= eta/2 (or any sharper target).  From
-- that bound and nonnegativity of 2^{-q}, this module reconstructs the exact
-- mature inverse-shell target required by Round 39.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain

scaleFreeDensityCoefficient :
  ∀ {effectiveViscosity shell} →
  Gain.InverseShellRestrictedGainDensity effectiveViscosity shell → ℚ
scaleFreeDensityCoefficient {shell = shell} certificate =
  Gain.density certificate * Sharp.dyadicScale shell

physicalHHBadGainDensityEqualsOneDerivativeFactorization :
  ∀ {effectiveViscosity shell}
    (certificate :
      Gain.InverseShellRestrictedGainDensity effectiveViscosity shell) →
  scaleFreeDensityCoefficient certificate * Sharp.inverseDyadicScale shell
  ≡ Gain.density certificate
physicalHHBadGainDensityEqualsOneDerivativeFactorization
    {shell = shell} certificate =
  let
    density = Gain.density certificate
    lambda = Sharp.dyadicScale shell
    mu = Sharp.inverseDyadicScale shell
    regroup :
      (density * lambda) * mu ≡ density * (mu * lambda)
    regroup = solve (density ∷ lambda ∷ mu ∷ [])
  in
  trans regroup
    (trans
      (cong (density *_) (Sharp.inverseDyadicReciprocal shell))
      (solve (density ∷ [])))

record ScaleFreeHHBadCoefficientBound
    {effectiveViscosity : ℚ}
    (eta : ℚ)
    (shell : Nat)
    (certificate :
      Gain.InverseShellRestrictedGainDensity effectiveViscosity shell) : Set where
  field
    coefficientBelowHalfEta :
      scaleFreeDensityCoefficient certificate ≤ eta * Sharp.half

open ScaleFreeHHBadCoefficientBound public

physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget :
  ∀ {effectiveViscosity eta shell}
    (certificate :
      Gain.InverseShellRestrictedGainDensity effectiveViscosity shell) →
  ScaleFreeHHBadCoefficientBound eta shell certificate →
  Gain.density certificate ≤ Sharp.requiredHHBadGain eta shell
physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget
    {eta = eta} {shell = shell} certificate coefficientBound =
  let
    coefficient = scaleFreeDensityCoefficient certificate
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    scaled :
      coefficient * mu ≤ (eta * Sharp.half) * mu
    scaled =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoʳ-≤-nonNeg mu
        (coefficientBelowHalfEta coefficientBound)

    leftMeaning : coefficient * mu ≡ Gain.density certificate
    leftMeaning =
      physicalHHBadGainDensityEqualsOneDerivativeFactorization certificate

    rightMeaning :
      (eta * Sharp.half) * mu ≡ Sharp.requiredHHBadGain eta shell
    rightMeaning = solve (eta ∷ Sharp.half ∷ mu ∷ [])
  in
  subst
    (λ lower → lower ≤ Sharp.requiredHHBadGain eta shell)
    leftMeaning
    (subst
      (λ upper → coefficient * mu ≤ upper)
      rightMeaning
      scaled)

physicalHHBadFactorizationIsAlgebraicNotAnalytic : Bool
physicalHHBadFactorizationIsAlgebraicNotAnalytic = true

physicalHHBadOnlyScaleFreeCoefficientBoundRemainsAnalytic : Bool
physicalHHBadOnlyScaleFreeCoefficientBoundRemainsAnalytic = true

physicalHHBadFactorizationIsAlgebraicNotAnalyticIsTrue :
  physicalHHBadFactorizationIsAlgebraicNotAnalytic ≡ true
physicalHHBadFactorizationIsAlgebraicNotAnalyticIsTrue = refl

physicalHHBadOnlyScaleFreeCoefficientBoundRemainsAnalyticIsTrue :
  physicalHHBadOnlyScaleFreeCoefficientBoundRemainsAnalytic ≡ true
physicalHHBadOnlyScaleFreeCoefficientBoundRemainsAnalyticIsTrue = refl
