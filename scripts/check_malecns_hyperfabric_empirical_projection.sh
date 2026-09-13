#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSTypedHyperfabricChartProjectionExact.agda"

required=(
  "MaleCNSHyperfabricProjectionReceipt"
  "676"
  "16250"
  "0.13639532298659035"
  "SenderGainHyperfabricProjectionReceipt"
  "0.13189851095808636"
  "maxAbsDifference"
  "0.0"
  "MaleCNSPhysicalIncidenceProjectionReceipt"
  "aggregatedDirectSupportCompleteAt26RegionQuotient"
  "aggregatedRegionSupportEqualsRawPhysicalSynapseHypergraph"
)

for needle in "${required[@]}"; do
  grep -Fq "$needle" "$owner" || {
    echo "missing MaleCNS hyperfabric empirical projection term: $needle" >&2
    exit 1
  }
done
