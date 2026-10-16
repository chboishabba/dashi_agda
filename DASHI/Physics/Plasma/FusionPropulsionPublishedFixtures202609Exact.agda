module DASHI.Physics.Plasma.FusionPropulsionPublishedFixtures202609Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Plasma.FusionPropulsionLiteralMaxCutExact as MaxCut

------------------------------------------------------------------------
-- SOURCE-INDEXED NUMERICAL TARGETS
--
-- Mantissa/exponent pairs preserve reported precision without inventing error
-- bars.  These are targets extracted from the cited sources, not measurements
-- produced by this repository.
------------------------------------------------------------------------

data ReportedUnit : Set where
  perCubicMetre : ReportedUnit
  kiloElectronVolt : ReportedUnit
  centimetre : ReportedUnit
  percent : ReportedUnit

record ReportedDecimal : Set where
  constructor reported-decimal
  field
    mantissa : Nat
    decimalPlaces : Nat
    baseTenExponent : Nat
    unit : ReportedUnit
    approximate : Bool
    reportedSource : MaxCut.SourceAttribution

open ReportedDecimal public

yingguangPeakIonDensityTarget : ReportedDecimal
yingguangPeakIonDensityTarget =
  reported-decimal
    22 1 22 perCubicMetre true MaxCut.zhuWuYingguang1Source

yingguangElectronTemperatureTarget : ReportedDecimal
yingguangElectronTemperatureTarget =
  reported-decimal
    17 1 0 kiloElectronVolt true MaxCut.zhuWuYingguang1Source

yingguangIonTemperatureTarget : ReportedDecimal
yingguangIonTemperatureTarget =
  reported-decimal
    12 1 0 kiloElectronVolt true MaxCut.zhuWuYingguang1Source

yingguangSeparatrixRadiusTarget : ReportedDecimal
yingguangSeparatrixRadiusTarget =
  reported-decimal
    1 0 0 centimetre true MaxCut.zhuWuYingguang1Source

qinfischCoherentProtonPowerFraction : ReportedDecimal
qinfischCoherentProtonPowerFraction =
  reported-decimal
    9996 2 0 percent false MaxCut.qinfischRootPoleSource

record PB11PlannedResonanceTargets : Set where
  constructor pb11-planned-resonance-targets
  field
    lowerLaboratoryEnergyKeV : Nat
    upperLaboratoryEnergyKeV : Nat
    plannedSource : MaxCut.SourceAttribution
    targetDevelopmentOnly : Bool
    targetDevelopmentOnlyIsTrue : targetDevelopmentOnly ≡ true
    newCrossSectionResultAvailable : Bool
    newCrossSectionResultAvailableIsFalse :
      newCrossSectionResultAvailable ≡ false

open PB11PlannedResonanceTargets public

pb11PlannedResonanceTargets : PB11PlannedResonanceTargets
pb11PlannedResonanceTargets =
  pb11-planned-resonance-targets
    160 600 MaxCut.rikenPB11TargetSource true refl false refl

record PublishedFixtureBoundary : Set where
  constructor published-fixture-boundary
  field
    approximateValueIsExactMeasurement : Bool
    approximateValueIsExactMeasurementIsFalse :
      approximateValueIsExactMeasurement ≡ false
    qinfischFractionIsExperimentalMeasurement : Bool
    qinfischFractionIsExperimentalMeasurementIsFalse :
      qinfischFractionIsExperimentalMeasurement ≡ false
    rikenTargetStatusIsCrossSectionResult : Bool
    rikenTargetStatusIsCrossSectionResultIsFalse :
      rikenTargetStatusIsCrossSectionResult ≡ false

canonicalPublishedFixtureBoundary : PublishedFixtureBoundary
canonicalPublishedFixtureBoundary =
  published-fixture-boundary false refl false refl false refl
