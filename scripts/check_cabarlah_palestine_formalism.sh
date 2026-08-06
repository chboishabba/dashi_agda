#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

if [[ "${CABARLAH_SKIP_ROUND5:-0}" != "1" ]]; then
  bash scripts/check_unification_round5.sh
fi

FILES=(
  DASHI/Physics/Foundations/CabarlahClaimStatusExact.agda
  DASHI/Physics/Foundations/CabarlahEvidenceWitnessExact.agda
  DASHI/Physics/Foundations/CabarlahHistoricalLayerExact.agda
  DASHI/Physics/Foundations/CabarlahToponymTranscriptionExact.agda
  DASHI/Physics/Foundations/CabarlahPhonologyEnvelopeExact.agda
  DASHI/Physics/Foundations/CabarlahSignalInferenceExact.agda
  DASHI/Physics/Foundations/SettlerEnemyAbstractionExact.agda
  DASHI/Physics/Foundations/IndigenousMilitaryIntelligenceCircuitExact.agda
  DASHI/Physics/Foundations/FrontierEnemyPersistenceExact.agda
  DASHI/Physics/Foundations/CabarlahPalestineSourceAtlas.agda
  DASHI/Physics/Foundations/CabarlahPalestineBoundary.agda
  DASHI/Physics/Foundations/CabarlahPalestineRegression.agda
  DASHI/Physics/Foundations/Everything.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  if [[ ! -f "$file" ]]; then
    echo "required Cabarlah-Palestine source is missing: $file" >&2
    exit 1
  fi

  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

# Correction guards: the superseded spellings and historical collapses must not
# be reintroduced in positive theorem positions.
grep -q 'capbarlahHistoricalSpelling = refuted' \
  DASHI/Physics/Foundations/CabarlahClaimStatusExact.agda
grep -q 'communistConcessionBoundaryAtCabarlah = refuted' \
  DASHI/Physics/Foundations/CabarlahClaimStatusExact.agda
grep -q 'noCommunistConcessionBoundaryWitness ()' \
  DASHI/Physics/Foundations/CabarlahEvidenceWitnessExact.agda
grep -q 'envelopeProductCountIsThirtyTwo' \
  DASHI/Physics/Foundations/CabarlahPhonologyEnvelopeExact.agda
grep -q 'finiteEnvelopeIsRecoveredLexiconIsFalse' \
  DASHI/Physics/Foundations/CabarlahPhonologyEnvelopeExact.agda
grep -q 'comparisonAuthority indigenousAustraliaSettlerStructure =' \
  DASHI/Physics/Foundations/SettlerEnemyAbstractionExact.agda
grep -q 'structuralHomologyOnly' \
  DASHI/Physics/Foundations/SettlerEnemyAbstractionExact.agda
grep -q 'crossDomainComparisonIsStructuralOnly' \
  DASHI/Physics/Foundations/CabarlahSignalInferenceExact.agda
grep -q 'canonicalCabarlahPalestineSourceCountIsTen' \
  DASHI/Physics/Foundations/CabarlahPalestineSourceAtlas.agda

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Foundations/CabarlahPalestineRegression.agda \
  DASHI/Physics/Foundations/CabarlahPalestineBoundary.agda \
  DASHI/Physics/Foundations/Everything.agda \
  DASHI/Unified/Everything.agda
