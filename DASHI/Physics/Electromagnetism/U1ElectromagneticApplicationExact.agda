module DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.Gauge.SUNPrimitives as SUN
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- ABELIAN ELECTROMAGNETIC APPLICATION SOCKET
--
-- Repository-native architecture owner.
--
-- This module does not derive Maxwell theory from the non-abelian SU(N) Clay
-- lane. It supplies the missing application-facing U(1)/electromagnetic socket
-- using the canonical SI quantity carrier, while requiring independent law,
-- gauge, boundary and validation references from any concrete application.
------------------------------------------------------------------------

data GaugeFamily : Set where
  abelianU1
  nonAbelianSUN
  : GaugeFamily

record U1ElectromagneticFieldSocket : Set₁ where
  constructor u1ElectromagneticFieldSocket
  field
    FieldState : Set

    voltageScale : SI.DecimalScale
    electricFieldScale : SI.DecimalScale
    magneticFieldScale : SI.DecimalScale
    chargeDensityScale : SI.DecimalScale
    currentDensityScale : SI.DecimalScale
    permittivityScale : SI.DecimalScale
    conductivityScale : SI.DecimalScale

    potential : FieldState → SI.Quantity SI.Voltage voltageScale
    electricField : FieldState → SI.Quantity SI.ElectricField electricFieldScale
    magneticFluxDensity : FieldState → SI.Quantity SI.MagneticFluxDensity magneticFieldScale
    chargeDensity : FieldState → SI.Quantity SI.ChargeDensity chargeDensityScale
    currentDensity : FieldState → SI.Quantity SI.CurrentDensity currentDensityScale
    permittivity : FieldState → SI.Quantity SI.Permittivity permittivityScale
    conductivity : FieldState → SI.Quantity SI.Conductivity conductivityScale

    gaugeConventionReference : String
    maxwellLawReference : String
    constitutiveMediumReference : String
    geometryBoundaryReference : String
    sourceCurrentReference : String
    validationReference : String

open U1ElectromagneticFieldSocket public

------------------------------------------------------------------------
-- A concrete reduction can explicitly identify a domain field with this U(1)
-- surface without promoting the SU(N) theorem lane into biological or
-- environmental electromagnetism.
------------------------------------------------------------------------

record U1ApplicationReduction : Set₁ where
  constructor u1ApplicationReduction
  field
    fieldSocket : U1ElectromagneticFieldSocket
    applicationOwner : String
    potentialIdentificationReference : String
    fieldIdentificationReference : String
    chargeCurrentIdentificationReference : String
    quasistaticOrDynamicRegimeReference : String
    scaleReductionReference : String
    experimentalValidationReference : String

open U1ApplicationReduction public

suNGaugePrecedentOwner : String
suNGaugePrecedentOwner = "DASHI.Geometry.Gauge.SUNPrimitives"

suNClayPromotionImported : Bool
suNClayPromotionImported = SUN.clayYangMillsPromoted

suNClayPromotionImportedIsFalse : suNClayPromotionImported ≡ false
suNClayPromotionImportedIsFalse = SUN.clayYangMillsPromotedIsFalse

record U1ElectromagneticBoundary : Set where
  constructor u1ElectromagneticBoundary
  field
    u1ElectromagnetismIsNonAbelianYangMills : Bool
    u1ElectromagnetismIsNonAbelianYangMillsIsFalse :
      u1ElectromagnetismIsNonAbelianYangMills ≡ false

    suNClayProofProvesApplicationElectromagnetism : Bool
    suNClayProofProvesApplicationElectromagnetismIsFalse :
      suNClayProofProvesApplicationElectromagnetism ≡ false

    siDimensionTypingProvesMaxwellLaw : Bool
    siDimensionTypingProvesMaxwellLawIsFalse :
      siDimensionTypingProvesMaxwellLaw ≡ false

    applicationReductionNeedsIndependentValidation : Bool
    applicationReductionNeedsIndependentValidationIsTrue :
      applicationReductionNeedsIndependentValidation ≡ true

canonicalU1ElectromagneticBoundary : U1ElectromagneticBoundary
canonicalU1ElectromagneticBoundary =
  u1ElectromagneticBoundary
    false refl
    false refl
    false refl
    true refl
