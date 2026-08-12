module DASHI.Physics.Closure.NSTriadKNHHBadInverseShellDensityFromSchurRound41Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: P. K. Mitter.
-- Title: "The Exact Renormalization Group".
-- Persistent identifier: 10.48550/arXiv.math-ph/0505008.
--
-- DASHI CONTRIBUTION
--
-- Connect Round 41's exact one-derivative Schur magnitude calculation to the
-- actual Round-39 HH-bad restricted-gain interface.  If the literal density
-- coefficient is the same object as
--
--   C_q = (L nu^-1 R) 2^-q
--
-- and the scale-free coefficient obeys
--
--   0 <= L nu^-1 R <= C_bad,
--
-- then
--
--   C_q <= C_bad 2^-q.
--
-- Supplying the already-physical restricted gain cells therefore constructs
-- Round 39's `InverseShellRestrictedGainDensity` certificate directly.  This
-- removes all remaining inverse-shell *algebra* from A6/A8.  What stays open
-- is the same-object PDE theorem identifying the bad gain density with the
-- one-derivative factorization and bounding its scale-free coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadOneDerivativeGainRound41Exact as OneD

record OneDerivativeInverseShellDensityCertificate
    (effectiveViscosity density : ℚ)
    (shell : Nat) : Set where
  field
    factorization : OneD.PhysicalHHBadOneDerivativeFactorization
    factorizationAtShell : OneD.shell factorization ≡ shell
    densitySameObject : density ≡ OneD.physicalGainDensity factorization

    scaleFreeConstant : ℚ
    scaleFreeCoefficientNonnegative :
      0ℚ ≤ OneD.normalizedTwoDerivativeSchurMagnitude
        (OneD.leftCoefficient factorization)
        (OneD.viscosityInverse factorization)
        (OneD.rightCoefficient factorization)
    scaleFreeConstantNonnegative : 0ℚ ≤ scaleFreeConstant
    scaleFreeCoefficientBound :
      OneD.normalizedTwoDerivativeSchurMagnitude
        (OneD.leftCoefficient factorization)
        (OneD.viscosityInverse factorization)
        (OneD.rightCoefficient factorization)
      ≤ scaleFreeConstant

    densityNonnegative : 0ℚ ≤ density
    cells : List (Gain.RestrictedGainDensityCell
      effectiveViscosity density shell)

open OneDerivativeInverseShellDensityCertificate public

schurInverseShellTarget :
  ∀ {effectiveViscosity density shell} →
  OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell → ℚ
schurInverseShellTarget {shell = shell} certificate =
  scaleFreeConstant certificate * Sharp.inverseDyadicScale shell

schurInverseShellTargetNonnegative :
  ∀ {effectiveViscosity density shell}
    (certificate : OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell) →
  0ℚ ≤ schurInverseShellTarget certificate
schurInverseShellTargetNonnegative {shell = shell} certificate =
  let
    inverseNN = Floor.inverseDyadicScaleNonnegative shell
    instance
      constantNNI = nonNegative (scaleFreeConstantNonnegative certificate)
      inverseNNI = nonNegative inverseNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (scaleFreeConstant certificate) (Sharp.inverseDyadicScale shell)
  in
  ℚP.nonNegative⁻¹
    (scaleFreeConstant certificate * Sharp.inverseDyadicScale shell)

densityBelowSchurInverseShellTarget :
  ∀ {effectiveViscosity density shell}
    (certificate : OneDerivativeInverseShellDensityCertificate
      effectiveViscosity density shell) →
  density ≤ schurInverseShellTarget certificate
densityBelowSchurInverseShellTarget
    {density = density} {shell = shell} certificate =
  let
    factorization = factorization certificate
    coefficient = OneD.normalizedTwoDerivativeSchurMagnitude
      (OneD.leftCoefficient factorization)
      (OneD.viscosityInverse factorization)
      (OneD.rightCoefficient factorization)
    inverse = Sharp.inverseDyadicScale shell
    inverseNN = Floor.inverseDyadicScaleNonnegative shell

    coefficientScaled :
      coefficient * inverse
      ≤ scaleFreeConstant certificate * inverse
    coefficientScaled =
      let instance inverseNNI = nonNegative inverseNN
      in ℚP.*-monoʳ-≤-nonNeg inverse
        (scaleFreeCoefficientBound certificate)

    physicalAtOwnShell :
      OneD.physicalGainDensity factorization
      ≡ coefficient * Sharp.inverseDyadicScale (OneD.shell factorization)
    physicalAtOwnShell =
      OneD.physicalOneDerivativeFactorizationExposesInverseShell factorization

    physicalAtSelectedShell :
      OneD.physicalGainDensity factorization ≡ coefficient * inverse
    physicalAtSelectedShell =
      subst
        (λ selectedShell →
          OneD.physicalGainDensity factorization
          ≡ coefficient * Sharp.inverseDyadicScale selectedShell)
        (factorizationAtShell certificate)
        physicalAtOwnShell

    densityMeaning : density ≡ coefficient * inverse
    densityMeaning = trans (densitySameObject certificate) physicalAtSelectedShell
  in
  subst
    (λ lower → lower ≤ schurInverseShellTarget certificate)
    (sym densityMeaning)
    coefficientScaled

asRound39InverseShellCertificate :
  ∀ {effectiveViscosity density shell} →
  (certificate : OneDerivativeInverseShellDensityCertificate
    effectiveViscosity density shell) →
  Gain.InverseShellRestrictedGainDensity effectiveViscosity shell
asRound39InverseShellCertificate
    {effectiveViscosity} {density} {shell} certificate = record
  { density = density
  ; densityNonnegative = densityNonnegative certificate
  ; inverseShellTarget = schurInverseShellTarget certificate
  ; inverseShellTargetNonnegative = schurInverseShellTargetNonnegative certificate
  ; densityBelowInverseShellTarget =
      densityBelowSchurInverseShellTarget certificate
  ; cells = cells certificate
  }

oneDerivativeSchurToInverseShellDensityClosed : Bool
oneDerivativeSchurToInverseShellDensityClosed = true

physicalHHBadGainDensitySchurSameObjectConstructed : Bool
physicalHHBadGainDensitySchurSameObjectConstructed = false

physicalHHBadScaleFreeCoefficientBoundConstructed : Bool
physicalHHBadScaleFreeCoefficientBoundConstructed = false

oneDerivativeSchurToInverseShellDensityClosedIsTrue :
  oneDerivativeSchurToInverseShellDensityClosed ≡ true
oneDerivativeSchurToInverseShellDensityClosedIsTrue = refl
