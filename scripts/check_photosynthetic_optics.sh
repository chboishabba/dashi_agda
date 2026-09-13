#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda/lib/stdlib}"

"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PlantHydraulicAtmosphereCarbonCouplingExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/ConstitutiveHydrologyPlantCalibrationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/SolarOpticalSiteFibreCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PhotosyntheticLightTransportCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/CanopySpectralRadiativeTransferExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PhotosyntheticLightOptimizationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/PhotosyntheticAssimilationValidationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/DashiRTXAdaptiveTransportSourceAtlasExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Environment/DashiRTXPhotosyntheticAdaptiveTransportCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/InverseCausticNumericalProducerExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Physics/Optics/LESOpticalNumericalWitnessCrossPollinationExact.agda
"$AGDA_BIN" -i . -i "$AGDA_STDLIB" DASHI/Architecture/ASMLSolarOpticalRealisationCrossPollinationExact.agda
