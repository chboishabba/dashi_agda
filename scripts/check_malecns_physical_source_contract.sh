#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/MaleCNSTypedHyperfabricChartProjectionExact.agda"

grep -q 'MaleCNSOfficialPhysicalSourceReceipt' "$owner"
grep -q 'male-cns:v1.0' "$owner"
grep -q 'connectome-weights-male-cns-v1.0-minconf-0.5.feather' "$owner"
grep -q 'syn-partners-male-cns-v1.0-minconf-0.5.feather' "$owner"
grep -q 'skeletons-unisex-template' "$owner"
grep -q 'fullConnectionGraphPaysRawSegmentConnectivity' "$owner"
grep -q 'jrc2018SkeletonProductPaysConnectivity' "$owner"
grep -q 'regionAggregationIsDerivedQuotient' "$owner"
