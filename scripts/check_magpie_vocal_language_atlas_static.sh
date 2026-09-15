#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OBS="DASHI/Biology/MagpieVocalAtlasObservationExact.agda"
LATENT="DASHI/Biology/MagpieVocalAtlasLatentExact.agda"
SEM="DASHI/Biology/MagpieSemanticPromotionExact.agda"
VALID="DASHI/Biology/BioacousticFlyStateSpaceValidation.agda"
ALL="DASHI/Biology/AnimalexicEverything.agda"

test -f "$OBS"
test -f "$LATENT"
test -f "$SEM"

grep -q "data VocalObservationLevel" "$OBS"
grep -q "data LocationPrecision" "$OBS"
grep -q "record MagpieVocalEvent" "$OBS"
grep -q "sourceTitleDoesNotCreateExactLocation" "$OBS"
grep -q "unknownIdentityRemainsFirstClass" "$OBS"

grep -q "latentSimilarityDoesNotCreateMeaning" "$LATENT"
grep -q "regionPredictabilityDoesNotCreateDialect" "$LATENT"
grep -q "groupSyntaxDoesNotCreateRegionalDialect" "$LATENT"
grep -q "recordingProvenance" "$LATENT"

grep -q "semanticCandidateDoesNotCreateInterventionAuthority" "$SEM"
grep -q "modelPredictionDoesNotCreateAnimalIntent" "$SEM"
grep -q "repeatedSelfPredictionDoesNotCreateIndependentCorroboration" "$SEM"

grep -q "MagpieVocalAtlasObservationExact" "$VALID"
grep -q "MagpieVocalAtlasLatentExact" "$VALID"
grep -q "MagpieSemanticPromotionExact" "$VALID"
grep -q "MagpieVocalAtlasObservationExact" "$ALL"
grep -q "MagpieVocalAtlasLatentExact" "$ALL"
grep -q "MagpieSemanticPromotionExact" "$ALL"

echo "magpie vocal language atlas static contract passed"
