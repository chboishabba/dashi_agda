#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact.agda"

required=(
  "ReplicationIdentityRecoveryReceipt"
  "559"
  "1061"
  "374"
  "185"
  "04032024_6f_a2_r5"
  "04192024_6f_a1_r9"
  "gauthey_lbm_identity_accumulation.json"
  "a9504ea00a30960a6728f90a5ff31b4d1f97ced6"
  "9d15d4acc622a87cdd0ebc5d2f22f8531b277ce7"
  "currentRecoveryImplementationCommit"
  "perTrialCheckpointingImplemented"
  "accumulatedReceiptAdvancesAfterEachTrial"
  "sourceZipMayBeReleasedOnlyAfterDurableCheckpoint"
  "implementationAdvanceCreatesEmpiricalPayment"
  "exactSourceIdentityRecoveryComplete"
  "sourceIdentityRecoveryImpliesIndependentTrialReplication"
  "sourceIdentityRecoveryImpliesJRC2018Ready"
)

for needle in "${required[@]}"; do
  grep -Fq "$needle" "$owner" || {
    echo "missing replication-acquisition contract term: $needle" >&2
    exit 1
  }
done
