#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$ROOT"

: "${DASHI_NO_TMUX:=1}"
: "${AGDA_RTS_HEAP:=7G}"
: "${DASHI_AGDA_RSS_LIMIT_MB:=8192}"

DASHI_NO_TMUX="$DASHI_NO_TMUX" AGDA_RTS_HEAP="$AGDA_RTS_HEAP" DASHI_AGDA_RSS_LIMIT_MB="$DASHI_AGDA_RSS_LIMIT_MB" ./scripts/run_agda29_parallel_check.sh   DASHI/Education/DigitalESDStudyParseInteropExact.agda   DASHI/Education/DigitalESDStudyParseInteropRegression.agda   DASHI/Education/DigitalESDStudyParseExecutionExact.agda   DASHI/Education/DigitalESDStudyParseExecutionRegression.agda
