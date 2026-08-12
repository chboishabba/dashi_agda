module DASHI.Physics.Closure.NSTriadKNHHBadInverseShellOwnerCostRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 33 proved that the raw HH-bad shell ratio is
--
--   R_q = 2 lambda_q,
--
-- so the unique exact gain calibrating a pre-threshold shell coefficient eta
-- is
--
--   (eta/2) lambda_q^-1.
--
-- Round 41 proved that a literal one-derivative Schur factorization has density
--
--   c_q = C_q lambda_q^-1,
--
-- where C_q is the scale-free coefficient L nu^-1 R.
--
-- This file composes those two exact statements instead of leaving the
-- constant bookkeeping informal.  On the same-object Round-41 certificate,
--
--   c_q R_q = 2 C_q
--
-- exactly.  Thus the *raw-ratio neutralization cost* is exactly 2 C_q before
-- scale-free majorization, and C_q <= C_bad gives
--
--   c_q R_q <= 2 C_bad.
--
-- IMPORTANT: 2 C_bad is not yet the final HH-bad owner viscosity tax.  The
-- directional bad-set threshold contributes the separate delta^-1 factor
-- already proved in Round 40.  The companion
-- `NSTriadKNHHBadThresholdedOwnerCostRound42Exact` composes both mechanisms and
-- gives the actual reserve coefficient 2 C_bad / delta.
--
-- This file therefore isolates the exact cost of the inverse-shell mechanism
-- itself.  A proof of the inverse shell power is still useless if the physical
-- scale-free C_bad is too large after the threshold tax is restored.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNLuoCriticalDissipationHHBadBridgeRound34Exact as Critical
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeGainRound41Exact as OneD
import DASHI.Physics.Closure.NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact as Density

scaleFreeCoefficient :
  ∀ {effectiveViscosity density shell} →
  Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell → ℚ
scaleFreeCoefficient certificate =
  OneD.normalizedTwoDerivativeSchurMagnitude
    (OneD.leftCoefficient (Density.factorization certificate))
    (OneD.viscosityInverse (Density.factorization certificate))
    (OneD.rightCoefficient (Density.factorization certificate))

literalDensityIsCoefficientTimesInverseShell :
  ∀ {effectiveViscosity density shell} →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  density ≡ scaleFreeCoefficient certificate * Sharp.inverseDyadicScale shell
literalDensityIsCoefficientTimesInverseShell
    {density = density} {shell = shell} certificate =
  let
    factorization = Density.factorization certificate

    physicalAtOwnShell :
      OneD.physicalGainDensity factorization
      ≡ scaleFreeCoefficient certificate
          * Sharp.inverseDyadicScale (OneD.shell factorization)
    physicalAtOwnShell =
      OneD.physicalOneDerivativeFactorizationExposesInverseShell factorization

    physicalAtSelectedShell :
      OneD.physicalGainDensity factorization
      ≡ scaleFreeCoefficient certificate * Sharp.inverseDyadicScale shell
    physicalAtSelectedShell =
      subst
        (λ selectedShell →
          OneD.physicalGainDensity factorization
          ≡ scaleFreeCoefficient certificate
              * Sharp.inverseDyadicScale selectedShell)
        (Density.factorizationAtShell certificate)
        physicalAtOwnShell
  in
  trans (Density.densitySameObject certificate) physicalAtSelectedShell

inverseShellDensityTimesRawRatioExact :
  ∀ {effectiveViscosity density shell} →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  density * Sharp.rawHHBadRatio shell
  ≡ Sharp.two * scaleFreeCoefficient certificate
inverseShellDensityTimesRawRatioExact
    {density = density} {shell = shell} certificate =
  let
    coefficient = scaleFreeCoefficient certificate
    inverse = Sharp.inverseDyadicScale shell
    lambda = Sharp.dyadicScale shell

    densityMeaning = literalDensityIsCoefficientTimesInverseShell certificate

    first :
      density * Sharp.rawHHBadRatio shell
      ≡ (coefficient * inverse) * (Sharp.two * lambda)
    first = cong (_* Sharp.rawHHBadRatio shell) densityMeaning

    regroup :
      (coefficient * inverse) * (Sharp.two * lambda)
      ≡ Sharp.two * coefficient * (inverse * lambda)
    regroup = solve (coefficient ∷ inverse ∷ lambda ∷ Sharp.two ∷ [])

    cancel :
      Sharp.two * coefficient * (inverse * lambda)
      ≡ Sharp.two * coefficient
    cancel =
      trans
        (cong (Sharp.two * coefficient *_)
          (Sharp.inverseDyadicReciprocal shell))
        (solve (Sharp.two ∷ coefficient ∷ []))
  in
  trans first (trans regroup cancel)

doubledScaleFreeCoefficientBelowDoubledBound :
  ∀ {effectiveViscosity density shell} →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  Sharp.two * scaleFreeCoefficient certificate
  ≤ Sharp.two * Density.scaleFreeConstant certificate
doubledScaleFreeCoefficientBelowDoubledBound certificate =
  let instance twoNN = nonNegative Critical.twoNonnegative
  in ℚP.*-monoˡ-≤-nonNeg Sharp.two
      (Density.scaleFreeCoefficientBound certificate)

inverseShellDensityRawRatioBelowDoubledConstant :
  ∀ {effectiveViscosity density shell} →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  density * Sharp.rawHHBadRatio shell
  ≤ Sharp.two * Density.scaleFreeConstant certificate
inverseShellDensityRawRatioBelowDoubledConstant certificate =
  subst
    (λ lower → lower ≤ Sharp.two * Density.scaleFreeConstant certificate)
    (sym (inverseShellDensityTimesRawRatioExact certificate))
    (doubledScaleFreeCoefficientBelowDoubledBound certificate)

inverseShellDensityFitsOwnerEta :
  ∀ {effectiveViscosity density shell} →
  (certificate : Density.OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  (eta : ℚ) →
  Sharp.two * Density.scaleFreeConstant certificate ≤ eta →
  density * Sharp.rawHHBadRatio shell ≤ eta
inverseShellDensityFitsOwnerEta certificate eta doubledConstantBelowEta =
  ℚP.≤-trans
    (inverseShellDensityRawRatioBelowDoubledConstant certificate)
    doubledConstantBelowEta

exactHHBadRawRatioCostFromOneDerivativeDensityClosed : Bool
exactHHBadRawRatioCostFromOneDerivativeDensityClosed = true

physicalHHBadRawRatioNeutralizationNeedsDoubledScaleFreeConstant : Bool
physicalHHBadRawRatioNeutralizationNeedsDoubledScaleFreeConstant = true

-- Backward-compatible names retained for the stacked Round-42 consumer.  They
-- refer only to the pre-threshold raw-ratio cost; the thresholded companion is
-- the actual nine-owner coefficient.
exactHHBadOwnerCostFromOneDerivativeDensityClosed : Bool
exactHHBadOwnerCostFromOneDerivativeDensityClosed =
  exactHHBadRawRatioCostFromOneDerivativeDensityClosed

physicalHHBadReserveNowNeedsDoubledScaleFreeConstant : Bool
physicalHHBadReserveNowNeedsDoubledScaleFreeConstant =
  physicalHHBadRawRatioNeutralizationNeedsDoubledScaleFreeConstant

exactHHBadOwnerCostFromOneDerivativeDensityClosedIsTrue :
  exactHHBadOwnerCostFromOneDerivativeDensityClosed ≡ true
exactHHBadOwnerCostFromOneDerivativeDensityClosedIsTrue = refl
