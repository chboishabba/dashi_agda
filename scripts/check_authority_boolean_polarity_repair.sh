#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/AuthorityBooleanPolarityRepairExact.agda"

[[ -f "$owner" ]]

grep -q 'record AuthorityBooleanPolarityRepair' "$owner"
grep -q 'legacyBlockedBooleanPolarityInverted' "$owner"
grep -q 'bodyMeasurementMindReadingBlocked' "$owner"
grep -q 'bodyMeasurementReverseInferenceBlocked' "$owner"
grep -q 'functionalConnectomeMindReadingBlocked' "$owner"
grep -q 'functionalConnectomeDiagnosisBlocked' "$owner"
grep -q 'functionalConnectomeTreatmentBlocked' "$owner"
grep -q 'fmriProxyMindReadingBlocked' "$owner"
grep -q 'fmriProxyHiddenChartRecoveryBlocked' "$owner"
grep -q 'blockedMeansAuthorityUnavailable' "$owner"
grep -q 'legacyFalseMeansBlockedIsDeprecated' "$owner"
