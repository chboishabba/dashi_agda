#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FILES=(
  DASHI/Core/PortableSemanticInterpretationExact.agda
  DASHI/Core/PortableSemanticInterpretationRegression.agda
  DASHI/Core/PortableInteractiveViewExact.agda
  DASHI/Core/PortableInteractiveViewRegression.agda
  DASHI/Core/PortableLoopInterpretationExact.agda
  DASHI/Core/PortableLoopInterpretationRegression.agda
  DASHI/Core/PortableSemanticConsumerAdequacyBridgeExact.agda
  DASHI/Core/PortableSemanticConsumerAdequacyRegression.agda
  DASHI/Core/PortableSemanticTranslationRealisationBridgeExact.agda
  DASHI/Core/PortableSemanticTranslationRealisationRegression.agda
  DASHI/Core/PortableSemanticInterpretationValidation.agda
)

FORBIDDEN_PATTERN='\{![^}]*!\}|(^|[[:space:]=:(])\?([[:space:];,)}]|$)|^[[:space:]]*postulate([[:space:]]|$)|--allow-unsolved-metas|\{-# OPTIONS[^#]*--(unsafe|type-in-type|no-positivity-check|no-termination-check|rewriting)([[:space:]]|#)|=[[:space:]]*_[[:space:]]*$'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required portable semantic source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "forbidden hole, postulate, placeholder, or unsafe option in $file" >&2
    exit 1
  fi
done

grep -q '^record SemanticInterpretationProblem' DASHI/Core/PortableSemanticInterpretationExact.agda
grep -q '^record SemanticRefinement' DASHI/Core/PortableSemanticInterpretationExact.agda
grep -q '^twoRefinementsGiveConsumerEquivalence :' DASHI/Core/PortableSemanticInterpretationExact.agda
grep -q '^canonicalActivationContract :' DASHI/Core/PortableInteractiveViewExact.agda
grep -q '^canonicalFrontendEquivalence :' DASHI/Core/PortableInteractiveViewExact.agda
grep -q '^jsAndGpuEquivalentForResult :' DASHI/Core/PortableLoopInterpretationExact.agda
grep -q '^canonicalDifferentExecutionStrategy :' DASHI/Core/PortableLoopInterpretationExact.agda
grep -q '^semanticAdequacyRequiredByEligibility :' DASHI/Core/PortableSemanticConsumerAdequacyBridgeExact.agda
grep -q '^refinementGivesAdequateFor :' DASHI/Core/PortableSemanticTranslationRealisationBridgeExact.agda

scripts/run_agda29_parallel_check.sh DASHI/Core/PortableSemanticInterpretationValidation.agda
