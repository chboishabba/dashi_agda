#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_projector_resolution_round3.sh

sources=(
  DASHI/Moonshine/MoonshineOrbifoldWeightTwoDecompositionExact.agda
  DASHI/Moonshine/MoonshineOrbifoldMasslessStateRemovalExact.agda
  DASHI/Moonshine/MoonshineZ3OrbifoldThreeLocalSiblingExact.agda
  DASHI/Moonshine/LeechWeightTwo196608AuthorityCorrectionExact.agda
  DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda
  DASHI/Moonshine/Monster3BKernelCharacterCriterionExact.agda
  DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda
  DASHI/Moonshine/Monster3BOrbifoldLocalModuleRound4Validation.agda
  DASHI/EverythingMonster3BOrbifoldLocalModuleRound4.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi

  if grep -Pzo '\{!.*?!\}' "$source" >/dev/null; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

weight2=DASHI/Moonshine/MoonshineOrbifoldWeightTwoDecompositionExact.agda
massless=DASHI/Moonshine/MoonshineOrbifoldMasslessStateRemovalExact.agda
siblings=DASHI/Moonshine/MoonshineZ3OrbifoldThreeLocalSiblingExact.agda
correction=DASHI/Moonshine/LeechWeightTwo196608AuthorityCorrectionExact.agda
multiplicity=DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda
character=DASHI/Moonshine/Monster3BKernelCharacterCriterionExact.agda
cocycle=DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda
validation=DASHI/Moonshine/Monster3BOrbifoldLocalModuleRound4Validation.agda
aggregate=DASHI/EverythingMonster3BOrbifoldLocalModuleRound4.agda

require_pattern "$weight2" 'untwistedInvariantWeightTwoDimensionIs98580'
require_pattern "$weight2" 'twistedInvariantWeightTwoDimensionIs98304'
require_pattern "$weight2" 'publishedOrbifoldWeightTwoSplit'
require_pattern "$weight2" 'monsterNontrivialWeightTwoDimensionIs196883'
require_pattern "$weight2" 'coordinateSubtotalIsNotUntwistedOrbifoldSummand'
require_pattern "$massless" 'directSumOfEmptyIsEmpty'
require_pattern "$massless" 'moonshineWeightOneEmpty'
require_pattern "$massless" 'conformalExcitationIndexIsTwo'
require_pattern "$massless" 'conformalIndexProvesFourDimensionalYangMillsGapIsFalse'
require_pattern "$siblings" 'siblingsShareOrbifoldOrigin'
require_pattern "$siblings" 'kernelGeometriesAreDistinct'
require_pattern "$siblings" 'siblingsShareRepresentedSectorDimension'
require_pattern "$correction" 'bothChartsReconstructWeightTwo'
require_pattern "$correction" 'coordinateChartIsPublishedFLMOrbifoldDecompositionIsFalse'
require_pattern "$multiplicity" 'canonicalModelMultiplicityEvaluationIsomorphism'
require_pattern "$multiplicity" 'multiplicityEmbeddingTranslationEquivariant'
require_pattern "$multiplicity" 'ActualZetaSectorRecognition'
require_pattern "$multiplicity" 'actualProjectorTranslationCovariant'
require_pattern "$multiplicity" 'actualStandardTranslationFixedPointFree'
require_pattern "$character" 'modelTraceIsNinetyHeisenbergCopies'
require_pattern "$character" 'ActualKernelCharacterCertificate'
require_pattern "$character" 'actualNoncentralTraceVanishes'
require_pattern "$character" 'actualKernelCharacterCertificateConstructedIsFalse'
require_pattern "$cocycle" 'phaseAssociative'
require_pattern "$cocycle" 'multiplicityInverseProjectiveLaw'
require_pattern "$cocycle" 'compensatedTensorActionIsHonestOnPureTensors'
require_pattern "$validation" 'publishedWeightTwoSectorSplit'
require_pattern "$aggregate" 'import DASHI.Everything'
require_pattern "$aggregate" 'Monster3BOrbifoldLocalModuleRound4Validation'

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Monster3BOrbifoldLocalModuleRound4Validation.agda \
  DASHI/EverythingMonster3BOrbifoldLocalModuleRound4.agda
