module DASHI.Environment.LESEnvironmentSIQuantityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.QuantitiesConservation as Environment
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- ENVIRONMENT QUANTITIES -> CANONICAL SI BRIDGE
--
-- SI authority is DASHI.Physics.Units.SI, source-calibrated to the BIPM SI
-- Brochure (DOI 10.59161/AUEZ1291).  This owner only adapts existing LES
-- application scales to that canonical dimension carrier.
------------------------------------------------------------------------

record PositiveRationalScale : Set where
  constructor positiveRationalScale
  field
    numerator : Nat
    denominatorPred : Nat

open PositiveRationalScale public

oneScale : PositiveRationalScale
oneScale = positiveRationalScale 1 0

sixtyScale : PositiveRationalScale
sixtyScale = positiveRationalScale 60 0

milliScale : PositiveRationalScale
milliScale = positiveRationalScale 1 999

microScale : PositiveRationalScale
microScale = positiveRationalScale 1 999999

record EnvironmentSIAdapter (u : Environment.Unit) : Set where
  constructor environmentSIAdapter
  field
    dimension : SI.Dimension
    scaleToCoherentSI : PositiveRationalScale
    scaleMeaning : String
    provenanceReference : String

open EnvironmentSIAdapter public

labourMinutesSI : EnvironmentSIAdapter Environment.labourMinutes
labourMinutesSI = environmentSIAdapter SI.Time sixtyScale "minute -> second" SI.siSourceDOI

machineMinutesSI : EnvironmentSIAdapter Environment.machineMinutes
machineMinutesSI = environmentSIAdapter SI.Time sixtyScale "minute -> second" SI.siSourceDOI

fuelMillilitresSI : EnvironmentSIAdapter Environment.fuelMillilitres
fuelMillilitresSI = environmentSIAdapter SI.Volume microScale "millilitre -> cubic metre" SI.siSourceDOI

waterLitresSI : EnvironmentSIAdapter Environment.waterLitres
waterLitresSI = environmentSIAdapter SI.Volume milliScale "litre -> cubic metre" SI.siSourceDOI

earthworkLitresSI : EnvironmentSIAdapter Environment.earthworkLitres
earthworkLitresSI = environmentSIAdapter SI.Volume milliScale "litre -> cubic metre" SI.siSourceDOI

rainfallMicrometresSI : EnvironmentSIAdapter Environment.rainfallMicrometres
rainfallMicrometresSI = environmentSIAdapter SI.Length microScale "micrometre -> metre" SI.siSourceDOI

nitrogenGramsSI : EnvironmentSIAdapter Environment.nitrogenGrams
nitrogenGramsSI = environmentSIAdapter SI.Mass milliScale "gram -> kilogram" SI.siSourceDOI

phosphorusGramsSI : EnvironmentSIAdapter Environment.phosphorusGrams
phosphorusGramsSI = environmentSIAdapter SI.Mass milliScale "gram -> kilogram" SI.siSourceDOI

carbonGramsSI : EnvironmentSIAdapter Environment.carbonGrams
carbonGramsSI = environmentSIAdapter SI.Mass milliScale "gram -> kilogram" SI.siSourceDOI

sedimentGramsSI : EnvironmentSIAdapter Environment.sedimentGrams
sedimentGramsSI = environmentSIAdapter SI.Mass milliScale "gram -> kilogram" SI.siSourceDOI

habitatSquareMetresSI : EnvironmentSIAdapter Environment.habitatSquareMetres
habitatSquareMetresSI = environmentSIAdapter SI.Area oneScale "square metre -> square metre" SI.siSourceDOI

cropGramsSI : EnvironmentSIAdapter Environment.cropGrams
cropGramsSI = environmentSIAdapter SI.Mass milliScale "gram -> kilogram" SI.siSourceDOI

emissionGramsCO2eSI : EnvironmentSIAdapter Environment.emissionGramsCO2e
emissionGramsCO2eSI =
  environmentSIAdapter SI.Mass milliScale "gram -> kilogram; CO2e remains an accounting interpretation layered over mass" SI.siSourceDOI

record EnvironmentSIQuantityBoundary : Set where
  constructor environmentSIQuantityBoundary
  field
    audCentsIsSIPhysicalQuantity : Bool
    audCentsIsSIPhysicalQuantityIsFalse : audCentsIsSIPhysicalQuantity ≡ false

    confidenceBasisPointsIsSIPhysicalQuantity : Bool
    confidenceBasisPointsIsSIPhysicalQuantityIsFalse :
      confidenceBasisPointsIsSIPhysicalQuantity ≡ false

    sameDimensionImpliesSameUnitScale : Bool
    sameDimensionImpliesSameUnitScaleIsFalse :
      sameDimensionImpliesSameUnitScale ≡ false

    physicalScaleIsExplicitRatherThanFreeTextOnly : Bool
    physicalScaleIsExplicitRatherThanFreeTextOnlyIsTrue :
      physicalScaleIsExplicitRatherThanFreeTextOnly ≡ true

    canonicalSIUnitsOwnerReused : Bool
    canonicalSIUnitsOwnerReusedIsTrue : canonicalSIUnitsOwnerReused ≡ true

canonicalEnvironmentSIQuantityBoundary : EnvironmentSIQuantityBoundary
canonicalEnvironmentSIQuantityBoundary =
  environmentSIQuantityBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
