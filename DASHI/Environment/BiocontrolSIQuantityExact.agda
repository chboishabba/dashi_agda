module DASHI.Environment.BiocontrolSIQuantityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Units.SI as SI
import DASHI.Environment.LESEnvironmentSIQuantityBridgeExact as EnvironmentSI

------------------------------------------------------------------------
-- BIOCONTROL / LES SI QUANTITY BRIDGE
--
-- Physical probe semantics reuse DASHI.Physics.Units.SI and the existing LES
-- environment-SI bridge. BIPM supplies SI dimensions, units and decimal scale
-- semantics only. It does not supply ecological observations, causal claims,
-- experiment identity, calibration data, or intervention authority.
------------------------------------------------------------------------

bipmSISource : Attr.AttributedSource
bipmSISource = Attr.mkDOISource
  "Bureau International des Poids et Mesures (BIPM)"
  "The International System of Units (SI), 9th edition, revision 4.01"
  "SI Brochure"
  "2026"
  "10.59161/AUEZ1291"
  "https://www.bipm.org/en/publications/si-brochure"
  Attr.institutionalSource
  "primary authority for SI dimensions, units and decimal-scale semantics only; ecological measurements and interpretations remain source-specific"
  Attr.publicAttribution

record BIPMSourceReceipt : Set₁ where
  constructor bipmSourceReceipt
  field
    source : Attr.AttributedSource
    snowball : Snowball.SourceRoleSnowballReceipt source

open BIPMSourceReceipt public

canonicalBIPMSourceReceipt : BIPMSourceReceipt
canonicalBIPMSourceReceipt = bipmSourceReceipt
  bipmSISource
  (Snowball.canonicalSourceRoleSnowballReceipt bipmSISource)

------------------------------------------------------------------------
-- Physical coordinate receipts.
--
-- A receipt pays dimension/unit/scale semantics. It intentionally does not
-- claim that a numeric field observation has been acquired unless the final bit
-- is separately true.
------------------------------------------------------------------------

record PhysicalCoordinateReceipt : Set₁ where
  constructor physicalCoordinateReceipt
  field
    coordinateName : String
    dimension : SI.Dimension
    decimalScale : SI.DecimalScale
    coherentUnit : SI.Unit dimension
    fieldUnitReading : String
    coherentSIReading : String
    metrologyProvenanceReference : String
    measurementProvenanceReference : String
    physicalSemanticsPaid : Bool
    exactNumericValuePaid : Bool

open PhysicalCoordinateReceipt public

------------------------------------------------------------------------
-- Dissolved oxygen and nutrient concentration.
--
-- mg/L has the same physical dimension as kg/m^3. Numerically,
-- 1 mg/L = 10^-3 kg/m^3, hence SI.milliScale on SI.Density.
------------------------------------------------------------------------

dissolvedOxygenReceipt : PhysicalCoordinateReceipt
dissolvedOxygenReceipt = physicalCoordinateReceipt
  "dissolved oxygen mass concentration"
  SI.Density
  SI.milliScale
  SI.kilogramPerCubicMetre
  "mg L⁻¹"
  "10⁻³ kg m⁻³ per mg L⁻¹"
  SI.siSourceDOI
  "site/time/sensor-specific dissolved-oxygen observation remains an empirical receipt"
  true
  false

nutrientConcentrationReceipt : PhysicalCoordinateReceipt
nutrientConcentrationReceipt = physicalCoordinateReceipt
  "dissolved or suspended nutrient mass concentration"
  SI.Density
  SI.milliScale
  SI.kilogramPerCubicMetre
  "mg L⁻¹ when the declared assay reports mass concentration"
  "10⁻³ kg m⁻³ per mg L⁻¹"
  SI.siSourceDOI
  "analyte identity, assay method, dissolved/total fraction and field value remain source-specific"
  true
  false

------------------------------------------------------------------------
-- Biomass, hydrologic flow and temperature nuisance coordinates.
------------------------------------------------------------------------

biomassMassReceipt : PhysicalCoordinateReceipt
biomassMassReceipt = physicalCoordinateReceipt
  "removed or retained water-hyacinth biomass mass"
  SI.Mass
  SI.milliScale
  SI.kilogram
  "g"
  "10⁻³ kg per g"
  SI.siSourceDOI
  "wet/dry mass basis and measured value must be declared by the field protocol"
  true
  false

hydrologicFlowReceipt : PhysicalCoordinateReceipt
hydrologicFlowReceipt = physicalCoordinateReceipt
  "waterbody inflow/outflow volumetric flow rate"
  SI.VolumetricFlowRate
  SI.unitScale
  SI.cubicMetrePerSecond
  "m³ s⁻¹"
  "m³ s⁻¹"
  SI.siSourceDOI
  "gauging method, location, averaging window and measured value remain site-specific"
  true
  false

temperatureReceipt : PhysicalCoordinateReceipt
temperatureReceipt = physicalCoordinateReceipt
  "water temperature nuisance coordinate"
  SI.Temperature
  SI.unitScale
  SI.kelvin
  "K"
  "K"
  SI.siSourceDOI
  "sensor calibration, depth, time and measured value remain site-specific"
  true
  false

------------------------------------------------------------------------
-- Reuse the existing LES SI bridge rather than creating a second metrology
-- authority surface for environmental quantities.
------------------------------------------------------------------------

existingLESEnvironmentSIBridge : EnvironmentSI.EnvironmentSIQuantityBoundary
existingLESEnvironmentSIBridge = EnvironmentSI.canonicalEnvironmentSIQuantityBoundary

------------------------------------------------------------------------
-- Boundary: unit semantics are an independent debt axis.
------------------------------------------------------------------------

record BiocontrolSIQuantityBoundary : Set₁ where
  constructor biocontrolSIQuantityBoundary
  field
    existingLESBridgeRetained : EnvironmentSI.EnvironmentSIQuantityBoundary

    sameSIDimensionImpliesSameEcologicalQuantity : Bool
    sameSIDimensionImpliesSameEcologicalQuantityIsFalse :
      sameSIDimensionImpliesSameEcologicalQuantity ≡ false

    categoricalEcologicalStateIsAutomaticallySIQuantity : Bool
    categoricalEcologicalStateIsAutomaticallySIQuantityIsFalse :
      categoricalEcologicalStateIsAutomaticallySIQuantity ≡ false

    unitSemanticsAutomaticallyPayFieldMeasurement : Bool
    unitSemanticsAutomaticallyPayFieldMeasurementIsFalse :
      unitSemanticsAutomaticallyPayFieldMeasurement ≡ false

    mgPerLScaleToCoherentDensityIsExplicit : Bool
    mgPerLScaleToCoherentDensityIsExplicitIsTrue :
      mgPerLScaleToCoherentDensityIsExplicit ≡ true

    bipmCitationCreatesEcologicalAuthority : Bool
    bipmCitationCreatesEcologicalAuthorityIsFalse :
      bipmCitationCreatesEcologicalAuthority ≡ false

    sourceSpecificAnalyteAndProtocolStillRequired : Bool
    sourceSpecificAnalyteAndProtocolStillRequiredIsTrue :
      sourceSpecificAnalyteAndProtocolStillRequired ≡ true

canonicalBiocontrolSIQuantityBoundary : BiocontrolSIQuantityBoundary
canonicalBiocontrolSIQuantityBoundary = biocontrolSIQuantityBoundary
  existingLESEnvironmentSIBridge
  false refl
  false refl
  false refl
  true refl
  false refl
  true refl

------------------------------------------------------------------------
-- Readings for the experiment-search lane.
------------------------------------------------------------------------

siForwardReading : String
siForwardReading =
  "A physical discriminator may enter active experiment search only with its declared dimension/unit/scale semantics; numeric field values remain separately sourced."

siReverseReading : String
siReverseReading =
  "If a downstream consumer requires a physical oxygen, concentration, flow, mass or temperature interpretation and the observation lacks unit semantics, reopen SI-unit debt without invalidating already-paid ecological identity/provenance coordinates."
