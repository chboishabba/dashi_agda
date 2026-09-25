{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPhysicalEinsteinCalibrationExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Physical

------------------------------------------------------------------------
-- TYPED PHYSICAL EINSTEIN CALIBRATION BOUNDARY
--
-- The repository already carries the SI convention
--
--   kappa = 8*pi*G/c^4
--
-- and a vendored CODATA diagnostic, but deliberately does not promote the
-- decimal diagnostic to an exact typed value.  The antigravity source->geometry
-- route therefore consumes a typed coupling only together with an explicit
-- authority/value receipt.
------------------------------------------------------------------------

record AcceptedTypedEinsteinCoupling : Set₁ where
  field
    coupling : ℚ
    couplingPositive : 0ℚ < coupling

    authorityCandidate :
      Physical.EinsteinPhysicalCouplingCandidate

    AcceptedAuthorityValue : Set
    acceptedAuthorityValue : AcceptedAuthorityValue

    ValueConventionWeld : Set
    valueConventionWeld : ValueConventionWeld

open AcceptedTypedEinsteinCoupling public

------------------------------------------------------------------------
-- PHYSICAL SOURCE -> DIMENSIONLESS KOTTLER AMPLITUDE
--
-- sourceMagnitude is the dimensionless finite-source readout.
-- stressEnergyPerSourceUnit converts one source unit to physical energy density.
-- lengthScale converts one model length unit to physical length.
--
-- Multiplication by kappa and lengthScale^2 therefore produces the
-- dimensionless curvature/cosmological amplitude consumed by the normalized
-- Kottler model.
------------------------------------------------------------------------

record SourceToPhysicalKottlerCalibration
    (sourceMagnitude targetAmplitude : ℚ) : Set₁ where
  field
    einstein :
      AcceptedTypedEinsteinCoupling

    stressEnergyPerSourceUnit :
      ℚ

    stressEnergyPerSourceUnitPositive :
      0ℚ < stressEnergyPerSourceUnit

    lengthScale :
      ℚ

    lengthScalePositive :
      0ℚ < lengthScale

    calibratedAmplitude :
      coupling einstein
      * stressEnergyPerSourceUnit
      * sourceMagnitude
      * (lengthScale * lengthScale)
      ≡ targetAmplitude

open SourceToPhysicalKottlerCalibration public

physicalAmplitude :
  ∀ {sourceMagnitude targetAmplitude} →
  SourceToPhysicalKottlerCalibration sourceMagnitude targetAmplitude →
  ℚ
physicalAmplitude {sourceMagnitude = sourceMagnitude} calibration =
  coupling (einstein calibration)
  * stressEnergyPerSourceUnit calibration
  * sourceMagnitude
  * (lengthScale calibration * lengthScale calibration)

physicalAmplitudeIsTarget :
  ∀ {sourceMagnitude targetAmplitude}
    (calibration :
      SourceToPhysicalKottlerCalibration sourceMagnitude targetAmplitude) →
  physicalAmplitude calibration ≡ targetAmplitude
physicalAmplitudeIsTarget = calibratedAmplitude
