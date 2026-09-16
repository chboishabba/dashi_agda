#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/FibreRoutingMaleCNSReplicationAcquisition859Exact.agda"

required=(
  "ReplicationAcquisition859Receipt"
  "currentReplicationAcquisition859Receipt"
  "859"
  "761"
  "300"
  "04032024_6f_a2_r5"
  "04192024_6f_a1_r9"
  "04192024_6f_a1_r2"
  "04032024_6f_a2_r1"
  "Princeton Data Commons official Gauthey mirror"
  "10.34770/s5hx-1x75"
  "a2r1SearchedZero"
  "a1r1ZenodoSourceGap"
  "a1r1PrincetonFallbackStillCandidate"
  "exactIdentityRecoveryImpliesIndependentTrialReplication"
  "baseIndependentTrialReplicationStillUnpaid"
)

for needle in "${required[@]}"; do
  grep -Fq "$needle" "$owner" || {
    echo "missing replication-acquisition contract term: $needle" >&2
    exit 1
  }
done

echo "MaleCNS replication acquisition 859 static contract present"
