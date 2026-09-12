#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/TypedHyperfabricConsumerReductionBridgeExact.agda"

[[ -f "$owner" ]]

grep -q 'record SelectedSectionCarrier' "$owner"
grep -q 'realizeSection' "$owner"
grep -q 'sectionReduction' "$owner"
grep -q 'ConsumerRelativeReduction' "$owner"
grep -q 'sectionCodeConsumerFuturePreserved' "$owner"
grep -q 'SectionCodeEqualityImpliesGlobalSectionIdentity' "$owner"
grep -q 'sectionCodeEqualityDoesNotImplyGlobalSectionIdentity' "$owner"
grep -q 'globalSectionUniverseIsNotForcedIntoSet' "$owner"
