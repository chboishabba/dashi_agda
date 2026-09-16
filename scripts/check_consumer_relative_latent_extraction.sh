#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/ConsumerRelativeLatentExtractionExact.agda"

[[ -f "$owner" ]]

grep -q 'CanExtractLatent' "$owner"
grep -q 'nonfactorabilityBlocksLatentExtraction' "$owner"
grep -q 'postprocessingCannotRecoverErasedLatent' "$owner"
grep -q 'decisionFineStateNotExtractableFromAction' "$owner"
grep -q 'record LatentExtractionFrontier' "$owner"
grep -q 'rememberedEventExtractionPaid' "$owner"
grep -q 'memoryInfluenceExtractionPaid' "$owner"
grep -q 'motorPolicyExtractionPaid' "$owner"
grep -q 'consumerMinimalityDoesNotEstablishPhysicalMinimality' "$owner"
