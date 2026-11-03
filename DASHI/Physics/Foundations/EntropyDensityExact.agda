{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.EntropyDensityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ENTROPY / INFORMATION DENSITY NORMALISATION SURFACE
--
-- This owner deliberately separates several normalisations that are often
-- conflated in prose.  It supplies a common typed interface, not a theorem
-- identifying thermodynamic entropy, Shannon information, residual/reopening
-- information, horizon entropy, or entropy production.
------------------------------------------------------------------------

data DensityNormalisation : Set where
  physicalVolume
  surfaceArea
  spacetimeVolume
  siteCount
  supportMeasure
  timeRate
  volumeTimeRate
    : DensityNormalisation

record EntropyDensitySurface : Set₁ where
  field
    EntropyAmount : Set
    SupportAmount : Set
    DensityValue : Set
    TimeAmount : Set

    entropyPerVolume : EntropyAmount → SupportAmount → DensityValue
    entropyPerArea : EntropyAmount → SupportAmount → DensityValue
    entropyPerSite : EntropyAmount → SupportAmount → DensityValue
    entropyProductionDensity :
      EntropyAmount → TimeAmount → SupportAmount → DensityValue

    residualInformation : Set
    residualInformationDensity :
      residualInformation → SupportAmount → DensityValue

    thermodynamicEntropyDensityIsResidualInformationDensity : Bool
    entropyPerVolumeIsEntropyPerArea : Bool
    entropyPerVolumeIsEntropyPerSite : Bool
    entropyDensityIsEntropyProductionDensity : Bool

------------------------------------------------------------------------
-- Generic semantic firewall.
------------------------------------------------------------------------

record EntropyDensityAuthorityBoundary : Set where
  constructor entropyDensityAuthorityBoundary
  field
    normalisationMustBeDeclared : Bool
    supportMeasureMustBeDeclared : Bool
    horizonSurfaceAreaNormalisationMustBeDeclared : Bool
    thermodynamicAndInformationEntropyNeedBridge : Bool
    residualInformationAndThermodynamicEntropyNeedBridge : Bool
    entropyDensityAndEntropyProductionNeedBridge : Bool
    entropyPerAreaIsNotEntropyPerVolume : Bool
    coarseEntropyDoesNotByItselfProveFineStateErasure : Bool
    entropyDensityDoesNotByItselfSourceCurvature : Bool
    interpretation : String

canonicalEntropyDensityAuthorityBoundary : EntropyDensityAuthorityBoundary
canonicalEntropyDensityAuthorityBoundary =
  entropyDensityAuthorityBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    "Entropy per volume, horizon/surface area, site or declared support are distinct normalisations. Entropy production per volume-time is another observable. Residual/reopening information density is a separate carrier until an explicit statistical or physical bridge identifies them."

entropyPerAreaIsNotEntropyPerVolume : Bool
entropyPerAreaIsNotEntropyPerVolume = true

------------------------------------------------------------------------
-- Named projection used by cross-domain consumers.
--
-- High entropy on a declared coarse observer is compatible with nontrivial
-- residual information in the corresponding fine-state fibre.  The precise
-- entropy and residual measures are supplied by a concrete consumer.
------------------------------------------------------------------------

record CoarseEntropyResidualCompatibility : Set where
  constructor coarseEntropyResidualCompatibility
  field
    coarseEntropyDefined : Bool
    residualInformationDefined : Bool
    highCoarseEntropyPermitsNontrivialResidual : Bool
    maximalCoarseEntropyImpliesResidualZero : Bool

canonicalCoarseEntropyResidualCompatibility :
  CoarseEntropyResidualCompatibility
canonicalCoarseEntropyResidualCompatibility =
  coarseEntropyResidualCompatibility true true true false
