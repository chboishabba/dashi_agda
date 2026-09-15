module DASHI.Environment.BiocontrolSIQuantityRegression where

import DASHI.Environment.BiocontrolSIQuantityExact as SIProbe

------------------------------------------------------------------------
-- RED regression: physical probes must carry canonical SI dimension/unit/scale
-- semantics without turning categorical ecology states into fake measurements.
------------------------------------------------------------------------

dissolvedOxygenUsesMassConcentrationDimension : SIProbe.PhysicalCoordinateReceipt
dissolvedOxygenUsesMassConcentrationDimension = SIProbe.dissolvedOxygenReceipt

nutrientConcentrationUsesMassConcentrationDimension : SIProbe.PhysicalCoordinateReceipt
nutrientConcentrationUsesMassConcentrationDimension = SIProbe.nutrientConcentrationReceipt

biomassUsesMassDimension : SIProbe.PhysicalCoordinateReceipt
biomassUsesMassDimension = SIProbe.biomassMassReceipt

hydrologicFlowUsesVolumetricFlowDimension : SIProbe.PhysicalCoordinateReceipt
hydrologicFlowUsesVolumetricFlowDimension = SIProbe.hydrologicFlowReceipt

temperatureUsesKelvinDimension : SIProbe.PhysicalCoordinateReceipt
temperatureUsesKelvinDimension = SIProbe.temperatureReceipt

siDoesNotCollapseEcologicalSemantics : SIProbe.BiocontrolSIQuantityBoundary
siDoesNotCollapseEcologicalSemantics = SIProbe.canonicalBiocontrolSIQuantityBoundary

bipmAttributionSnowballs : SIProbe.BIPMSourceReceipt
bipmAttributionSnowballs = SIProbe.canonicalBIPMSourceReceipt
