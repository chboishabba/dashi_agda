#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_base369_process_hyperfabric_round6.sh

sources=(
  DASHI/Foundations/Base369NonaryTritSquareExact.agda
  DASHI/Foundations/Base369CompletedRelationalDigitExact.agda
  DASHI/Foundations/Base369FiveModePhaseQuotientExact.agda
  DASHI/Foundations/Base369RelationalSymmetryRealisationExact.agda
  DASHI/Moonshine/MonsterOggNonarySSPTritBridgeExact.agda
  DASHI/Moonshine/Monster3BBalancedRegularFibreExact.agda
  DASHI/Moonshine/MonsterOggPrimaryDepthAndNestedEigenCarrierExact.agda
  DASHI/Foundations/Base369OggNestedPhaseRound7Validation.agda
  DASHI/EverythingBase369OggNestedPhaseRound7.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source: $source" >&2
    exit 1
  fi

  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi

  if grep -Pzoq '(?s)\{!.*?!\}' "$source"; then
    echo "forbidden multiline hole in $source" >&2
    exit 1
  fi
done

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Base369OggNestedPhaseRound7Validation.agda \
  DASHI/EverythingBase369OggNestedPhaseRound7.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
