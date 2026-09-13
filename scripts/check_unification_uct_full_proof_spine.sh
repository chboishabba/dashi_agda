#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

scripts/run_agda29_parallel_check.sh \
  DASHI/Physics/Closure/UnificationUCTFullProofSpineValidation.agda
