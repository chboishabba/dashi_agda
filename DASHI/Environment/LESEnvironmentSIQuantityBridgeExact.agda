module DASHI.Environment.LESEnvironmentSIQuantityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.QuantitiesConservation as Environment
import DASHI.Physics.SIQuantitiesExact as SI

------------------------------------------------------------------------
-- ENVIRONMENT QUANTITIES -> SI DIMENSION BRIDGE
--
-- Source calibration for SI dimensions and unit relations is inherited from
-- DASHI.Physics.SIQuantitiesExact (BIPM SI Brochure, DOI 10.59161/AUEZ1291).
--
-- The existing Environment quantity owner intentionally uses application-scale
-- units such as litres, grams, minutes and micrometres.  This module does not
-- replace that owner.  It gives each physical unit a typed SI dimension and an
-- exact rational scale to the coherent SI unit for that dimension.
------------------------------------------------------------------------

-- Positive rational scale numerator/(denominatorPred+1).
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
labourMinutesSI =
  environmentSIAdapter SI.timeDimension sixtyScale "minute -> second" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

machineMinutesSI : EnvironmentSIAdapter Environment.machineMinutes
machineMinutesSI =
  environmentSIAdapter SI.timeDimension sixtyScale "minute -> second" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

-- 1 mL = 10^-6 m^3.
fuelMillilitresSI : EnvironmentSIAdapter Environment.fuelMillilitres
fuelMillilitresSI =
  environmentSIAdapter SI.volumeDimension microScale "millilitre -> cubic metre" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

-- 1 L = 10^-3 m^3.
waterLitresSI : EnvironmentSIAdapter Environment.waterLitres
waterLitresSI =
  environmentSIAdapter SI.volumeDimension milliScale "litre -> cubic metre" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

earthworkLitresSI : EnvironmentSIAdapter Environment.earthworkLitres
earthworkLitresSI =
  environmentSIAdapter SI.volumeDimension milliScale "litre -> cubic metre" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

-- 1 micrometre = 10^-6 m.
rainfallMicrometresSI : EnvironmentSIAdapter Environment.rainfallMicrometres
rainfallMicrometresSI =
  environmentSIAdapter SI.lengthDimension microScale "micrometre -> metre" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

-- 1 g = 10^-3 kg.
nitrogenGramsSI : EnvironmentSIAdapter Environment.nitrogenGrams
nitrogenGramsSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

phosphorusGramsSI : EnvironmentSIAdapter Environment.phosphorusGrams
phosphorusGramsSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

carbonGramsSI : EnvironmentSIAdapter Environment.carbonGrams
carbonGramsSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

sedimentGramsSI : EnvironmentSIAdapter Environment.sedimentGrams
sedimentGramsSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

habitatSquareMetresSI : EnvironmentSIAdapter Environment.habitatSquareMetres
habitatSquareMetresSI =
  environmentSIAdapter SI.areaDimension oneScale "square metre -> square metre" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

cropGramsSI : EnvironmentSIAdapter Environment.cropGrams
cropGramsSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

emissionGramsCO2eSI : EnvironmentSIAdapter Environment.emissionGramsCO2e
emissionGramsCO2eSI =
  environmentSIAdapter SI.massDimension milliScale "gram -> kilogram; CO2e remains an accounting interpretation layered over mass" "BIPM SI dimension source + application accounting provenance"

------------------------------------------------------------------------
-- Economic and confidence units intentionally do not receive SI adapters here.
------------------------------------------------------------------------

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

    environmentalPhysicalUnitsHaveExplicitSIWelds : Bool
    environmentalPhysicalUnitsHaveExplicitSIWeldsIsTrue :
      environmentalPhysicalUnitsHaveExplicitSIWelds ≡ true

canonicalEnvironmentSIQuantityBoundary : EnvironmentSIQuantityBoundary
canonicalEnvironmentSIQuantityBoundary =
  environmentSIQuantityBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
