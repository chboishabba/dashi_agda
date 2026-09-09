#!/usr/bin/env bash
set -euo pipefail

AGDA_BIN="${AGDA_BIN:-agda}"
AGDA_STDLIB="${AGDA_STDLIB:-/usr/share/agda/lib/stdlib}"

check() {
  "$AGDA_BIN" -i . -i "$AGDA_STDLIB" "$1"
}

# Existing LES fidelity / physics substrate.
check DASHI/Environment/LatentDepthFormalism.agda
check DASHI/Environment/SurrogateCalibration.agda
check DASHI/Environment/LESDomainBasisBidiFrontierExact.agda
check DASHI/Environment/LESFluidPhysicsCouplingExact.agda

# Existing optics / photosynthesis / dashiRTX lane.
check DASHI/Physics/Optics/GeometricalOpticsRefractionLensPrismExact.agda
check DASHI/Physics/Optics/DashiRTXAdaptiveTransportSourceAtlasExact.agda
check DASHI/Environment/PhotosyntheticLightTransportCrossPollinationExact.agda
check DASHI/Environment/CanopySpectralRadiativeTransferExact.agda
check DASHI/Environment/PhotosyntheticLightOptimizationExact.agda
check DASHI/Environment/DashiRTXPhotosyntheticAdaptiveTransportCrossPollinationExact.agda

# General LES physical-world-engine continuation.
check DASHI/Environment/LESPhysicalPhotonTransportFibreExact.agda
check DASHI/Environment/LESWaterPhotonInteractionExact.agda
check DASHI/Environment/LESMultiphysicsFidelityEscalationExact.agda
check DASHI/Environment/LESPhysicalWorldEngineRTXCrossPollinationExact.agda

# Physically based VFX / coupled impact scene.
check DASHI/Environment/LESVFXPhysicalOperationsExact.agda
check DASHI/Environment/LESGodzillaFrigateMultiphysicsSceneExact.agda

# Aggregate integration surface.
check DASHI/Environment/Everything.agda
