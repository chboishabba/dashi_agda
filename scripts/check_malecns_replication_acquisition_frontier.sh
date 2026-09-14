#!/usr/bin/env bash
set -euo pipefail

owner="DASHI/Reasoning/FibreRoutingMaleCNSMagnitudeAssignmentReplicationFrontierExact.agda"

required=(
  "ReplicationIdentityRecoveryReceipt"
  "SearchedZeroTrialReceipt"
  "a2r1SearchedZeroReceipt"
  "559"
  "1061"
  "374"
  "185"
  "currentSearchedTrialCount = 3"
  "04032024_6f_a2_r5"
  "04192024_6f_a1_r9"
  "04032024_6f_a2_r1"
  "gauthey_lbm_identity_accumulation.json"
  "86db813616584477ec88efced3b33a1dd94fc637"
  "8f8bf0b834069c0ede282ec79290fccbb1f9fcad"
  "currentRecoveryImplementationCommit"
  "perTrialCheckpointingImplemented"
  "accumulatedReceiptAdvancesAfterEachTrial"
  "sourceZipMayBeReleasedOnlyAfterDurableCheckpoint"
  "searchedZeroRetainedAsInformation"
  "searchedZeroPromotesNoBiologicalContribution"
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
