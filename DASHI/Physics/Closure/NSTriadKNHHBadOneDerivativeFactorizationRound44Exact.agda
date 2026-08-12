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
-- followed by a shell-uniform bound on C_q.  The factorization itself is
-- algebraic.  For any literal Round-39 density g_q define
--
--   C_q := g_q 2^q.
--
-- The exact dyadic reciprocal law gives C_q 2^{-q} = g_q.  Therefore the only
-- genuinely analytic scalar obligation is C_q <= eta/2 (or a sharper bound).
-- This file starts *before* InverseShellRestrictedGainDensity, so the argument
-- is non-circular: a scale-free coefficient bound constructs the mature
-- Round-39 inverse-shell certificate rather than assuming it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain

scaleFreeDensityCoefficient : ℚ → Nat → ℚ
scaleFreeDensityCoefficient density shell =
  density * Sharp.dyadicScale shell

physicalHHBadGainDensityEqualsOneDerivativeFactorization :
  ∀ density shell →
  scaleFreeDensityCoefficient density shell
    * Sharp.inverseDyadicScale shell
  ≡ density
physicalHHBadGainDensityEqualsOneDerivativeFactorization density shell =
  let
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

record PhysicalHHBadOneDerivativeDensityInput
    (effectiveViscosity eta : ℚ)
    (shell : Nat) : Set where
  field
    density : ℚ
    densityNonnegative : 0ℚ ≤ density
    cells : List
      (Gain.RestrictedGainDensityCell effectiveViscosity density shell)

    physicalHHBadScaleFreeCoefficientBound :
      scaleFreeDensityCoefficient density shell ≤ eta * Sharp.half

open PhysicalHHBadOneDerivativeDensityInput public

physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget :
  ∀ {effectiveViscosity eta shell}
    (input : PhysicalHHBadOneDerivativeDensityInput
      effectiveViscosity eta shell) →
  density input ≤ Sharp.requiredHHBadGain eta shell
physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget
    {eta = eta} {shell = shell} input =
  let
    coefficient = scaleFreeDensityCoefficient (density input) shell
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell

    scaled :
      coefficient * mu ≤ (eta * Sharp.half) * mu
    scaled =
      let instance muNNI = nonNegative muNN
      in ℚP.*-monoʳ-≤-nonNeg mu
        (physicalHHBadScaleFreeCoefficientBound input)

    leftMeaning : coefficient * mu ≡ density input
    leftMeaning =
      physicalHHBadGainDensityEqualsOneDerivativeFactorization
        (density input) shell

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

asRound39InverseShellCertificate :
  ∀ {effectiveViscosity eta shell} →
  PhysicalHHBadOneDerivativeDensityInput effectiveViscosity eta shell →
  Gain.InverseShellRestrictedGainDensity effectiveViscosity shell
asRound39InverseShellCertificate
    {eta = eta} {shell = shell} input = record
  { density = density input
  ; densityNonnegative = densityNonnegative input
  ; inverseShellTarget = Sharp.requiredHHBadGain eta shell
  ; inverseShellTargetNonnegative =
      ℚP.≤-trans
        (densityNonnegative input)
        (physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget input)
  ; densityBelowInverseShellTarget =
      physicalHHBadScaleFreeCoefficientBoundImpliesDensityTarget input
  ; cells = cells input
  }

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
