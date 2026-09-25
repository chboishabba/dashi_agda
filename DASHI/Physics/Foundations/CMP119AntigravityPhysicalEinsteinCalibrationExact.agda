{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPhysicalEinsteinCalibrationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Physical
import DASHI.Promotion.NumericMeasuredAuthorityTokenNormalization as Numeric

------------------------------------------------------------------------
-- NORMALIZED RATIONAL CALIBRATION + MEASURED PHYSICAL COUPLING BOUNDARY
--
-- The exact antigravity geometry is rational.  The SI Einstein coupling is not:
--
--   kappa = 8*pi*G/c^4
--
-- contains transcendental pi and measured G.  Therefore an exact rational
-- "physical kappa" is a category error.  Keep the exact rational geometry and
-- its scale factor separate from a typed enclosure/authority receipt for the
-- measured physical coupling.
------------------------------------------------------------------------

record NormalizedEinsteinCoupling : Set where
  field
    coupling : ℚ
    couplingPositive : 0ℚ < coupling

open NormalizedEinsteinCoupling public

record SourceToNormalizedKottlerCalibration
    (sourceMagnitude targetAmplitude : ℚ) : Set where
  field
    einstein : NormalizedEinsteinCoupling

    stressEnergyPerSourceUnit : ℚ
    stressEnergyPerSourceUnitPositive :
      0ℚ < stressEnergyPerSourceUnit

    lengthScale : ℚ
    lengthScalePositive :
      0ℚ < lengthScale

    calibratedAmplitude :
      coupling einstein
      * stressEnergyPerSourceUnit
      * sourceMagnitude
      * (lengthScale * lengthScale)
      ≡ targetAmplitude

open SourceToNormalizedKottlerCalibration public

normalizedAmplitude :
  ∀ {sourceMagnitude targetAmplitude} →
  SourceToNormalizedKottlerCalibration sourceMagnitude targetAmplitude →
  ℚ
normalizedAmplitude {sourceMagnitude = sourceMagnitude} calibration =
  coupling (einstein calibration)
  * stressEnergyPerSourceUnit calibration
  * sourceMagnitude
  * (lengthScale calibration * lengthScale calibration)

normalizedAmplitudeIsTarget :
  ∀ {sourceMagnitude targetAmplitude}
    (calibration :
      SourceToNormalizedKottlerCalibration sourceMagnitude targetAmplitude) →
  normalizedAmplitude calibration ≡ targetAmplitude
normalizedAmplitudeIsTarget = calibratedAmplitude

------------------------------------------------------------------------
-- MEASURED PHYSICAL COUPLING AS AN ENCLOSURE.
--
-- The rational endpoints are proof carriers for an enclosure; they are not a
-- claim that kappa itself is rational.  Accepted authority remains a distinct
-- type, matching EinsteinPhysicalCouplingCalibrationExact.
------------------------------------------------------------------------

record PhysicalEinsteinCouplingInterval : Set where
  field
    lower upper : ℚ
    lowerPositive : 0ℚ < lower
    ordered : lower ≤ upper

open PhysicalEinsteinCouplingInterval public

record AcceptedPhysicalEinsteinCoupling
    (interval : PhysicalEinsteinCouplingInterval) : Set₁ where
  field
    authorityCandidate :
      Physical.EinsteinPhysicalCouplingCandidate

    AcceptedMeasuredAuthority : Set
    acceptedMeasuredAuthority : AcceptedMeasuredAuthority

    UncertaintyContained : Set
    uncertaintyContained : UncertaintyContained

    EnergyDensityConventionWeld : Set
    energyDensityConventionWeld : EnergyDensityConventionWeld

    KappaDefinitionWeld : Set
    kappaDefinitionWeld : KappaDefinitionWeld

open AcceptedPhysicalEinsteinCoupling public

record PhysicalScaleEnclosure
    (sourceMagnitude : ℚ)
    (kappa : PhysicalEinsteinCouplingInterval) : Set where
  field
    stressEnergyLower stressEnergyUpper : ℚ
    lengthLower lengthUpper : ℚ

    stressLowerPositive : 0ℚ < stressEnergyLower
    stressOrdered : stressEnergyLower ≤ stressEnergyUpper

    lengthLowerPositive : 0ℚ < lengthLower
    lengthOrdered : lengthLower ≤ lengthUpper

open PhysicalScaleEnclosure public

physicalAmplitudeLower :
  ∀ {sourceMagnitude kappa} →
  PhysicalScaleEnclosure sourceMagnitude kappa → ℚ
physicalAmplitudeLower {sourceMagnitude = sourceMagnitude} {kappa = kappa} scale =
  lower kappa
  * stressEnergyLower scale
  * sourceMagnitude
  * (lengthLower scale * lengthLower scale)

physicalAmplitudeUpper :
  ∀ {sourceMagnitude kappa} →
  PhysicalScaleEnclosure sourceMagnitude kappa → ℚ
physicalAmplitudeUpper {sourceMagnitude = sourceMagnitude} {kappa = kappa} scale =
  upper kappa
  * stressEnergyUpper scale
  * sourceMagnitude
  * (lengthUpper scale * lengthUpper scale)

record PhysicalKottlerCalibrationEnclosure
    (sourceMagnitude targetAmplitude : ℚ)
    (kappa : PhysicalEinsteinCouplingInterval) : Set₁ where
  field
    authority :
      AcceptedPhysicalEinsteinCoupling kappa

    scale :
      PhysicalScaleEnclosure sourceMagnitude kappa

    targetAboveLower :
      physicalAmplitudeLower scale ≤ targetAmplitude

    targetBelowUpper :
      targetAmplitude ≤ physicalAmplitudeUpper scale

open PhysicalKottlerCalibrationEnclosure public

------------------------------------------------------------------------
-- TYPED CODATA DIAGNOSTIC ENCLOSURE
--
-- Exact rational endpoints corresponding to the vendored candidate
--
--   2.0766474428449717e-43 +/- 4.667112902128249e-48 m J^-1.
--
-- These endpoints type the diagnostic interval only.  They do not inhabit
-- AcceptedPhysicalEinsteinCoupling.
------------------------------------------------------------------------

codataCandidateKappaLower : ℚ
codataCandidateKappaLower =
  (+ 207660077171595041751)
  / 1000000000000000000000000000000000000000000000000000000000000000

codataCandidateKappaUpper : ℚ
codataCandidateKappaUpper =
  (+ 207669411397399298249)
  / 1000000000000000000000000000000000000000000000000000000000000000

codataCandidateKappaLowerPositive :
  0ℚ < codataCandidateKappaLower
codataCandidateKappaLowerPositive =
  ℚP.positive⁻¹ codataCandidateKappaLower

codataCandidateKappaOrdered :
  codataCandidateKappaLower ≤ codataCandidateKappaUpper
codataCandidateKappaOrdered =
  ℚP.≤ᵇ⇒≤ tt

codataCandidateKappaInterval :
  PhysicalEinsteinCouplingInterval
codataCandidateKappaInterval = record
  { PhysicalEinsteinCouplingInterval.lower =
      codataCandidateKappaLower
  ; PhysicalEinsteinCouplingInterval.upper =
      codataCandidateKappaUpper
  ; PhysicalEinsteinCouplingInterval.lowerPositive =
      codataCandidateKappaLowerPositive
  ; PhysicalEinsteinCouplingInterval.ordered =
      codataCandidateKappaOrdered
  }

record TypedKappaDiagnosticProvenance : Set where
  field
    sourceCandidate :
      Physical.EinsteinPhysicalCouplingCandidate

    interval :
      PhysicalEinsteinCouplingInterval

    sourceCandidateIsCanonical :
      sourceCandidate
      ≡ Physical.canonicalEinsteinPhysicalCouplingCandidate

    intervalIsCanonical :
      interval ≡ codataCandidateKappaInterval

    acceptedAuthorityStillFalse :
      Numeric.acceptedAuthorityTokenPresent Numeric.gNormalizedToken
      ≡ false

    numericValueLoadedStillFalse :
      Numeric.numericValueLoaded Numeric.gNormalizedToken
      ≡ false

    numericValuePromotedStillFalse :
      Numeric.numericValuePromoted Numeric.gNormalizedToken
      ≡ false

open TypedKappaDiagnosticProvenance public

canonicalTypedKappaDiagnosticProvenance :
  TypedKappaDiagnosticProvenance
canonicalTypedKappaDiagnosticProvenance = record
  { TypedKappaDiagnosticProvenance.sourceCandidate =
      Physical.canonicalEinsteinPhysicalCouplingCandidate
  ; TypedKappaDiagnosticProvenance.interval =
      codataCandidateKappaInterval
  ; TypedKappaDiagnosticProvenance.sourceCandidateIsCanonical =
      refl
  ; TypedKappaDiagnosticProvenance.intervalIsCanonical =
      refl
  ; TypedKappaDiagnosticProvenance.acceptedAuthorityStillFalse =
      Numeric.acceptedAuthorityTokenPresentIsFalse Numeric.gNormalizedToken
  ; TypedKappaDiagnosticProvenance.numericValueLoadedStillFalse =
      Numeric.numericValueLoadedIsFalse Numeric.gNormalizedToken
  ; TypedKappaDiagnosticProvenance.numericValuePromotedStillFalse =
      Numeric.numericValuePromotedIsFalse Numeric.gNormalizedToken
  }

------------------------------------------------------------------------
-- STATUS / TRUST BOUNDARY
------------------------------------------------------------------------

exactRationalPhysicalEinsteinCouplingClaimed : Bool
exactRationalPhysicalEinsteinCouplingClaimed = false

exactRationalPhysicalEinsteinCouplingClaimedIsFalse :
  exactRationalPhysicalEinsteinCouplingClaimed ≡ false
exactRationalPhysicalEinsteinCouplingClaimedIsFalse = refl

measuredCouplingIntervalABICompiled : Bool
measuredCouplingIntervalABICompiled = true

measuredCouplingIntervalABICompiledIsTrue :
  measuredCouplingIntervalABICompiled ≡ true
measuredCouplingIntervalABICompiledIsTrue = refl

acceptedMeasuredGCouplingStillRequired : Bool
acceptedMeasuredGCouplingStillRequired = true

acceptedMeasuredGCouplingStillRequiredIsTrue :
  acceptedMeasuredGCouplingStillRequired ≡ true
acceptedMeasuredGCouplingStillRequiredIsTrue = refl

stressEnergyScaleStillRequired : Bool
stressEnergyScaleStillRequired = true

stressEnergyScaleStillRequiredIsTrue :
  stressEnergyScaleStillRequired ≡ true
stressEnergyScaleStillRequiredIsTrue = refl

physicalLengthScaleStillRequired : Bool
physicalLengthScaleStillRequired = true

physicalLengthScaleStillRequiredIsTrue :
  physicalLengthScaleStillRequired ≡ true
physicalLengthScaleStillRequiredIsTrue = refl
