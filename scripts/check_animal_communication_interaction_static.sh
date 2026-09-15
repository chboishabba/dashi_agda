#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SCENE="DASHI/Biology/AnimalCommunicationSceneObservationExact.agda"
INTERACTION="DASHI/Biology/AnimalCommunicationInteractionExact.agda"
LATENT="DASHI/Biology/AnimalCommunicationLatentExact.agda"
SEMANTIC="DASHI/Biology/AnimalCommunicationSemanticEvidenceExact.agda"
MAGPIE="DASHI/Biology/MagpieAnimalCommunicationAdapterExact.agda"
VISUAL="DASHI/Biology/AnimalCommunicationMultiObserverVisualBridgeExact.agda"
ACOUSTIC="DASHI/Biology/AnimalCommunicationPassiveAcousticLocalizationExact.agda"
AVWELD="DASHI/Biology/AnimalCommunicationSharedWorldAVAssociationExact.agda"

for owner in "$SCENE" "$INTERACTION" "$LATENT" "$SEMANTIC" "$MAGPIE" "$VISUAL" "$ACOUSTIC" "$AVWELD"; do
  test -f "$owner"
done

grep -q "record AnimalCommunicationScene" "$SCENE"
grep -q "record EmitterCandidate" "$SCENE"
grep -q "scenePresenceCannotAssignEmitter" "$SCENE"
grep -q "record AcousticPropagationReceipt" "$SCENE"
grep -q "record SignalMixtureObservation" "$SCENE"
grep -q "simultaneousEmitterCandidates" "$SCENE"
grep -q "sensorMixtureCannotDetermineUniqueEmitterDecomposition" "$SCENE"
grep -q "propagationMediumDoesNotCreateEmitterIdentity" "$SCENE"
grep -q "interferenceDoesNotCreateInteraction" "$SCENE"
grep -q "manyToManyAVAssociationRetained" "$SCENE"
grep -q "record InteractionTurn" "$INTERACTION"
grep -q "receiverResponse" "$INTERACTION"
grep -q "signalFormCannotDetermineAddressee" "$INTERACTION"
grep -q "signalContextCannotDetermineResponse" "$INTERACTION"
grep -q "data CommunicationQuery" "$LATENT"
grep -q "crossSpeciesAnalogyDoesNotCreateSameMechanism" "$LATENT"
grep -q "responsePredictionDoesNotCreateMeaning" "$SEMANTIC"
grep -q "magpieAdapterDoesNotPromoteSemantics" "$MAGPIE"

grep -q "record MultiObserverAnimalTrackReceipt" "$VISUAL"
grep -q "dynamicTargetDoesNotCreateCameraPose" "$VISUAL"
grep -q "sameWorldTrackDoesNotCreateSpeciesIdentity" "$VISUAL"
grep -q "speciesIdentityDoesNotCreateIndividualIdentity" "$VISUAL"
grep -q "visualTrackDoesNotCreateVocalEmitterIdentity" "$VISUAL"

grep -q "record PassiveAcousticLocalizationReceipt" "$ACOUSTIC"
grep -q "timeDifferenceOfArrivalReference" "$ACOUSTIC"
grep -q "microphoneGeometryReference" "$ACOUSTIC"
grep -q "localizedCallDoesNotCreateUniqueBird" "$ACOUSTIC"
grep -q "tdoaFitDoesNotCreateSpeciesIdentity" "$ACOUSTIC"
grep -q "activeProbeUsed" "$ACOUSTIC"

grep -q "record SharedWorldAVAssociationReceipt" "$AVWELD"
grep -q "spatialOverlapDoesNotCreateSameEmitter" "$AVWELD"
grep -q "lowWorldWeldResidualDoesNotCreateSameAnimal" "$AVWELD"
grep -q "avAssociationDoesNotCreateSemanticMeaning" "$AVWELD"
grep -q "manyToManyAssociationRetained" "$AVWELD"

echo "animal communication interaction static contract passed"
