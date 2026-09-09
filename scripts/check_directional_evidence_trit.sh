#!/usr/bin/env bash
set -euo pipefail

FILES=(
  DASHI/Statistics/DirectionalEvidenceTritExact.agda
  DASHI/Statistics/DirectionalInferenceDesignExact.agda
  DASHI/Statistics/BinaryTestDecisionDirectionalEvidenceExact.agda
  DASHI/Statistics/HypothesisRegionGeometryExact.agda
  DASHI/Statistics/StandardBinaryTestRegionAdaptersExact.agda
  DASHI/Statistics/ConfidenceIntervalRegionEvidenceExact.agda
  DASHI/Statistics/StandardConfidenceIntervalInterpretationExact.agda
  DASHI/Statistics/Vec15BinaryDecisionDirectionalEvidenceBridgeExact.agda
  DASHI/Statistics/DirectionalEvidenceEverything.agda
  DASHI/Biology/LogisticPopulationDirectionalEvidenceExact.agda
  DASHI/Biology/LogisticAgenticPrebioticCrossPollinationExact.agda
  DASHI/AgenticMaterialBidiEverything.agda
  DASHI/Interop/DirectionalEvidenceProofSearchBridgeExact.agda
)

FORBIDDEN_PATTERN='(^|[[:space:]])postulate([[:space:]]|$)|\{!|!\}|TERMINATING|NO_TERMINATION_CHECK|allow-unsolved-metas|--no-positivity-check|--no-termination-check|NON_COVERING|--type-in-type|trustMe|primTrustMe'

for file in "${FILES[@]}"; do
  [[ -f "$file" ]] || { echo "required directional-evidence source is missing: $file" >&2; exit 1; }
  if grep -nE "$FORBIDDEN_PATTERN" "$file"; then
    echo "directional-evidence source contains forbidden proof escape hatch: $file" >&2
    exit 1
  fi
done

if command -v agda >/dev/null 2>&1; then
  for file in "${FILES[@]}"; do
    agda -i . -i /usr/share/agda-stdlib "$file"
  done
fi

echo "directional evidence / logistic population / agentic-prebiotic cross-pollination checks passed"
