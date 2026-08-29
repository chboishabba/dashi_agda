module DASHI.Environment.LESEnvironmentSIQuantityBridgeExact where

open import DASHI.Core.Prelude

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
-- explicit scale/conversion reference so those ledgers can be welded to fluid,
-- chemistry and bioelectric models without confusing unit scale with dimension.
------------------------------------------------------------------------

record EnvironmentSIAdapter (u : Environment.Unit) : Set where
  constructor environmentSIAdapter
  field
    dimension : SI.Dimension
    scaleToSIReference : String
    provenanceReference : String

open EnvironmentSIAdapter public

labourMinutesSI : EnvironmentSIAdapter Environment.labourMinutes
labourMinutesSI =
  environmentSIAdapter SI.timeDimension "1 min = 60 s" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

machineMinutesSI : EnvironmentSIAdapter Environment.machineMinutes
machineMinutesSI =
  environmentSIAdapter SI.timeDimension "1 min = 60 s" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

fuelMillilitresSI : EnvironmentSIAdapter Environment.fuelMillilitres
fuelMillilitresSI =
  environmentSIAdapter SI.volumeDimension "millilitre volume scale; convert to cubic metre before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

waterLitresSI : EnvironmentSIAdapter Environment.waterLitres
waterLitresSI =
  environmentSIAdapter SI.volumeDimension "litre volume scale; convert to cubic metre before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

earthworkLitresSI : EnvironmentSIAdapter Environment.earthworkLitres
earthworkLitresSI =
  environmentSIAdapter SI.volumeDimension "litre volume scale; convert to cubic metre before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

rainfallMicrometresSI : EnvironmentSIAdapter Environment.rainfallMicrometres
rainfallMicrometresSI =
  environmentSIAdapter SI.lengthDimension "micrometre length scale; convert to metre before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

nitrogenGramsSI : EnvironmentSIAdapter Environment.nitrogenGrams
nitrogenGramsSI =
  environmentSIAdapter SI.massDimension "gram mass scale; convert to kilogram before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

phosphorusGramsSI : EnvironmentSIAdapter Environment.phosphorusGrams
phosphorusGramsSI =
  environmentSIAdapter SI.massDimension "gram mass scale; convert to kilogram before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

carbonGramsSI : EnvironmentSIAdapter Environment.carbonGrams
carbonGramsSI =
  environmentSIAdapter SI.massDimension "gram mass scale; convert to kilogram before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

sedimentGramsSI : EnvironmentSIAdapter Environment.sedimentGrams
sedimentGramsSI =
  environmentSIAdapter SI.massDimension "gram mass scale; convert to kilogram before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

habitatSquareMetresSI : EnvironmentSIAdapter Environment.habitatSquareMetres
habitatSquareMetresSI =
  environmentSIAdapter SI.areaDimension "square metre area" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

cropGramsSI : EnvironmentSIAdapter Environment.cropGrams
cropGramsSI =
  environmentSIAdapter SI.massDimension "gram mass scale; convert to kilogram before physical coupling" "BIPM SI Brochure; DOI 10.59161/AUEZ1291"

emissionGramsCO2eSI : EnvironmentSIAdapter Environment.emissionGramsCO2e
emissionGramsCO2eSI =
  environmentSIAdapter SI.massDimension "gram mass scale; CO2e remains an accounting interpretation layered over mass" "BIPM SI dimension source + application accounting provenance"

------------------------------------------------------------------------
-- Economic and confidence units intentionally do not receive SI adapters here.
-- They are not physical dimensions merely because they are numeric.
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
