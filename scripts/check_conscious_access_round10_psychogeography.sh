#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
export AGDA_JOBS="${AGDA_JOBS:-1}"

bash scripts/check_conscious_access_round9_moonshine_modular_orbifold.sh

files=(
  DASHI/Biology/PsychogeographicFieldExact.agda
  DASHI/Biology/PsychogeographicMemoryHyperfabricExact.agda
  DASHI/Biology/PsychogeographicHexagramObservationExact.agda
  DASHI/Biology/MovingLineLearningTransportExact.agda
  DASHI/Biology/TraumaPsychogeographicMetricExact.agda
  DASHI/Biology/TraumaSensitiveDeriveExact.agda
  DASHI/Biology/UrbanPolyphonyThoughtCabinetExact.agda
  DASHI/Biology/RuinNarrativeReorganisationExact.agda
  DASHI/Biology/DiscoElysiumPsychogeographyExact.agda
  DASHI/Biology/PsychogeographicFilteredScaleExact.agda
  DASHI/Biology/PsychogeographicYijingDeriveExact.agda
  DASHI/Biology/PlaceMemorySinthomeReorganisationExact.agda
  DASHI/Biology/PsychogeographyYijingSourceAtlas.agda
  DASHI/Biology/PsychogeographyYijingBoundary.agda
  DASHI/Biology/PsychogeographyYijingRegression.agda
  DASHI/Biology/PsychogeographyEverything.agda
  DASHI/Biology/ConsciousAccessRound10PsychogeographyValidation.agda
)

for file in "${files[@]}"; do test -f "$file"; done

if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe|standardImported' "${files[@]}"; then
  echo "round ten contains a hole, postulate, unsafe escape, trust primitive, or imported theorem receipt" >&2
  exit 1
fi

checks=(
  'PsychogeographicFieldExact.agda:sameEndpointDoesNotForceSamePhase'
  'PsychogeographicFieldExact.agda:canonicalDetournementChangesUse'
  'PsychogeographicFieldExact.agda:sameMaterialCategoryNeedNotHaveSameLivedPotential'
  'PsychogeographicMemoryHyperfabricExact.agda:placeRevaluationPreservesRememberedEvent'
  'PsychogeographicMemoryHyperfabricExact.agda:placeExtinctionPreservesRememberedEvent'
  'PsychogeographicHexagramObservationExact.agda:projectionLosesPathInformation'
  'PsychogeographicHexagramObservationExact.agda:sameStateReversedReadsYang'
  'PsychogeographicHexagramObservationExact.agda:canonicalThresholdReadingAuthorityIsAssociative'
  'PsychogeographicHexagramObservationExact.agda:canonicalAnticipatedEncounteredDifferenceIsTwo'
  'MovingLineLearningTransportExact.agda:movingProjectionCommutes'
  'MovingLineLearningTransportExact.agda:canonicalMovingLearningResult'
  'TraumaPsychogeographicMetricExact.agda:physicalAndPsychogeographicMetricsNeedNotAgree'
  'TraumaPsychogeographicMetricExact.agda:typedObstructionUsesPlaceMemoryEdge'
  'TraumaSensitiveDeriveExact.agda:productiveFailureChangesSemanticState'
  'UrbanPolyphonyThoughtCabinetExact.agda:samePassageSupportsPolyphonicReadings'
  'UrbanPolyphonyThoughtCabinetExact.agda:canonicalCabinetHasTwoActiveThoughts'
  'UrbanPolyphonyThoughtCabinetExact.agda:sameUrbanSignalCanRedirectRoute'
  'UrbanPolyphonyThoughtCabinetExact.agda:thoughtDeactivationRetainsProvenance'
  'UrbanPolyphonyThoughtCabinetExact.agda:routeCanCompileDifferentIdentity'
  'RuinNarrativeReorganisationExact.agda:feedbackLoopClosesInFourSteps'
  'RuinNarrativeReorganisationExact.agda:ruinReorganisationDeclaresNoStalkErasure'
  'DiscoElysiumPsychogeographyExact.agda:crossTalkPreservesContentWhileWeakeningProvenance'
  'DiscoElysiumPsychogeographyExact.agda:loopRetainsNontrivialResidual'
  'PsychogeographicFilteredScaleExact.agda:wholeCarrierMixCrossesLowerUpperBoundary'
  'PsychogeographicYijingDeriveExact.agda:canonicalDeriveDifferenceIsTwo'
  'PlaceMemorySinthomeReorganisationExact.agda:placeReorganisationIsNotErasure'
  'PsychogeographyYijingSourceAtlas.agda:sourceAtlasHasTenRecords'
)

for check in "${checks[@]}"; do
  file="${check%%:*}"
  theorem="${check#*:}"
  grep -q "$theorem" "DASHI/Biology/$file"
done

grep -q '10.1037/0033-295X.103.4.670' DASHI/Biology/PsychogeographyYijingSourceAtlas.agda
grep -q '10.2307/2928520' DASHI/Biology/PsychogeographyYijingSourceAtlas.agda
grep -q '10.1111/j.1540-6253.2008.00475.x' DASHI/Biology/PsychogeographyYijingSourceAtlas.agda
grep -q '10.3390/rel17070796' DASHI/Biology/PsychogeographyYijingSourceAtlas.agda
grep -q '10.48550/arXiv.2309.17116' DASHI/Biology/PsychogeographyYijingSourceAtlas.agda

grep -q 'castEntailsExternalPrediction' DASHI/Biology/PsychogeographyYijingBoundary.agda
grep -q 'associationIsRecoveredMemoryAuthority' DASHI/Biology/PsychogeographyYijingBoundary.agda
grep -q 'cityLiterallyThinksClaimed' DASHI/Biology/PsychogeographyYijingBoundary.agda
grep -q 'fictionalPaleIsPhysicalCosmology' DASHI/Biology/PsychogeographyYijingBoundary.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Biology/ConsciousAccessRound10PsychogeographyValidation.agda
