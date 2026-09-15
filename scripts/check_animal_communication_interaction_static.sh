#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

SCENE="DASHI/Biology/AnimalCommunicationSceneObservationExact.agda"
INTERACTION="DASHI/Biology/AnimalCommunicationInteractionExact.agda"
LATENT="DASHI/Biology/AnimalCommunicationLatentExact.agda"
SEMANTIC="DASHI/Biology/AnimalCommunicationSemanticEvidenceExact.agda"
MAGPIE="DASHI/Biology/MagpieAnimalCommunicationAdapterExact.agda"

for owner in "$SCENE" "$INTERACTION" "$LATENT" "$SEMANTIC" "$MAGPIE"; do
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

echo "animal communication interaction static contract passed"
