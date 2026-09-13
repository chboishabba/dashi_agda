#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda/lib/stdlib}"

"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/GeometricalOpticsRefractionLensPrismExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/CausticFreeformSourceAtlasExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/AsphericSagSurfaceNormalExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/CatastropheDiffractionNormalFormExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/AsphericCausticManipulationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/InverseCausticNumericalProducerExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/OpticalSurfaceManufacturingToleranceExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/LESOpticalNumericalWitnessCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/LESOpticalSurrogateEscalationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/SolarOpticalSiteFibreCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PlantHydraulicAtmosphereCarbonCouplingExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/ConstitutiveHydrologyPlantCalibrationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PhotosyntheticLightTransportCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/PhotosyntheticOpticalCrossPollinationValidation.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileMechanicalDimensionExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileMechanicalFibreExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/LinearElasticTextileLawExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/QuasiStaticTextileLoadTransferExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileFailureSlipPredicateExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/FiniteTextileEquilibriumNetworkExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/BendingTorsionTextileLawExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/KineticSlipEvolutionExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/DiscreteTextileFracturePropagationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileEmpiricalCalibrationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/EffectiveFabricResponseExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/FabricDrapeCalibrationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileOpticalTransportBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileLustreObservationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileColourAppearanceBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileAngularAppearanceExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileSpectralReflectanceTransmittanceExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextilePolarisationTransportExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileFiberBRDFRealisationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileBirefringenceRetardanceExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileIridescentAppearanceExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileMechanicsOpticsCouplingExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileRefractiveOpticalTrainExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileReflectiveDiffractiveOpticalTrainExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/TextileCausticManipulationBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/TextileStitchHyperfabricExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/TextileStitchOperationalSemanticsExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/CircularKnittingHelicalLoopBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Topology/CrochetHookMicroSemanticsExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/JacquardPhysicalFibreBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Textile/StitchPhysicalFibreBridgeExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/TextilePhysicsValidation.agda
