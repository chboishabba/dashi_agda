#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

exec "$SCRIPT_DIR/run_agda29_parallel_check.sh" \
  DASHI/Physics/YangMills/BalabanClayGate4Validation.agda \
  DASHI/Physics/YangMills/BalabanClayConstructiveProducerAdvance.agda \
  DASHI/Physics/YangMills/BalabanClayGate4AndNumericalAuditCompletionLedger.agda \
  DASHI/Physics/YangMills/BalabanClayBranchHeadReceiptSurface.agda \
  DASHI/Physics/Closure/NSPeriodicOfficialCompletionRegression.agda
