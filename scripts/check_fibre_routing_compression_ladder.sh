#!/usr/bin/env bash
set -euo pipefail

python3 scripts/consumer_compression_observable.py --self-test

scripts/run_agda29_parallel_check.sh \
  DASHI/Reasoning/FibreRoutingCompressionLadderValidation.agda
