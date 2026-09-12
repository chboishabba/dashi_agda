#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSTypedHyperfabricChartProjectionExact.agda"

[[ -f "$owner" ]]

grep -q 'MaleCNSPairChartCode' "$owner"
grep -q 'realizeMaleCNSPairChartCode' "$owner"
grep -q 'maleCNSSelectedSectionCarrier' "$owner"
grep -q 'SelectedSectionCarrier' "$owner"
grep -q 'sectionPairChartRealizationExact' "$owner"
grep -q 'selectedSectionCarrierIsChartCodeNotPhysicalIncidence' "$owner"
