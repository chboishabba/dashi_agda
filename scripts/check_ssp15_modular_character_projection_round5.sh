#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_ssp15_indexed_weave_modular_round4.sh

sources=(
  DASHI/Biology/CoarseFineTenSectorProjectionExact.agda
  DASHI/Biology/D4NineCellOrbitCompressionExact.agda
  DASHI/Moonshine/ModularCurveJFrickeInterfaceExact.agda
  DASHI/Moonshine/Monster3BC3RepresentationRingEvaluationExact.agda
  DASHI/Moonshine/MonsterOrderExponentCorrectionExact.agda
  DASHI/Moonshine/SSPModularCharacterProjectionRound5Validation.agda
  DASHI/EverythingSSPModularCharacterProjectionRound5.agda
)

for source in "${sources[@]}"; do
  if [ ! -s "$source" ]; then
    echo "missing or empty source $source" >&2
    exit 1
  fi
  if grep -nE '(^|[[:space:]])postulate([[:space:]]|$)|--allow-unsolved-metas|--no-termination-check|--no-positivity-check|--type-in-type|--omega-in-omega|--rewriting|--unsafe|TERMINATING|NON_COVERING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|trustMe|primTrustMe|(^|[[:space:]])\?([[:space:];)]|$)' "$source"; then
    echo "forbidden trust escape or hole in $source" >&2
    exit 1
  fi
  if grep -Pzo '\{!.*?!\}' "$source" >/dev/null; then
    echo "forbidden interaction hole in $source" >&2
    exit 1
  fi
done

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

exponents=DASHI/Moonshine/MonsterOrderExponentCorrectionExact.agda
projection=DASHI/Biology/CoarseFineTenSectorProjectionExact.agda
d4=DASHI/Biology/D4NineCellOrbitCompressionExact.agda
modular=DASHI/Moonshine/ModularCurveJFrickeInterfaceExact.agda
c3=DASHI/Moonshine/Monster3BC3RepresentationRingEvaluationExact.agda
validation=DASHI/Moonshine/SSPModularCharacterProjectionRound5Validation.agda
top=DASHI/EverythingSSPModularCharacterProjectionRound5.agda

require_pattern "$exponents" '"Modular Functions and the Monstrous Exponents"'
require_pattern "$exponents" 'DOI: 10.48550/arXiv.2602.09135.'
require_pattern "$exponents" 'monsterOrderExponent Lane.p13 = 3'
require_pattern "$exponents" 'monsterOrderExponent Lane.p17 = 1'
require_pattern "$exponents" 'legacyDepthP13IsNotCorrect'
require_pattern "$exponents" 'modularValuationContribution 3 5 1 refl'
require_pattern "$exponents" 'modularValuationContribution 1 2 0 refl'
require_pattern "$projection" 'averageBroadcast'
require_pattern "$projection" 'projectCommonIdempotentAt'
require_pattern "$projection" 'fineResidualHasZeroSum'
require_pattern "$projection" 'commonResidualOrthogonal'
require_pattern "$projection" 'commonResidualNormSplit'
require_pattern "$projection" 'record NineRelativeField'
require_pattern "$d4" 'nineCellOrbitCount'
require_pattern "$d4" 'decodeAfterEncode'
require_pattern "$d4" 'encodeAfterDecode'
require_pattern "$d4" 'd4IrrepKindCountIsFive'
require_pattern "$modular" 'frickeSwapsSource'
require_pattern "$modular" 'observeUnorientedIsFrickeInvariant'
require_pattern "$modular" 'record OggPrimeModularPackage'
require_pattern "$c3" 'balancedC3Character'
require_pattern "$c3" 'monster3BDimensionIs196883'
require_pattern "$c3" 'monster3BGeneratorTraceIs53'
require_pattern "$c3" 'moonshineV2TraceAt3BIs54'
require_pattern "$c3" 'coefficientTenDerivedByRepresentationRingIsFalse'
require_pattern "$validation" 'validationResidual'
require_pattern "$top" 'import DASHI.Moonshine.MonsterOrderExponentCorrectionExact'

mkdir -p artifacts
python3 scripts/classify_agda_substance.py \
  --fail-on-external \
  --output artifacts/ssp15-modular-character-projection-round5.json \
  "${sources[@]}"

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/SSPModularCharacterProjectionRound5Validation.agda \
  DASHI/EverythingSSPModularCharacterProjectionRound5.agda
