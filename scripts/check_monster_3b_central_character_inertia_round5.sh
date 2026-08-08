#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_orbifold_local_module_round4.sh

sources=(
  DASHI/Moonshine/Monster3BCentralCharacterInertiaExact.agda
  DASHI/Moonshine/MonsterOggNonaryProbeAuthorityExact.agda
  DASHI/Moonshine/Monster3BActualZetaPromotionPipelineExact.agda
  DASHI/Moonshine/Monster3BMultiplicityTwelveSeventyEightRecognitionExact.agda
  DASHI/Moonshine/Monster3BCentralCharacterInertiaRound5Validation.agda
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
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

require_pattern() {
  local source="$1"
  local pattern="$2"
  if ! grep -F "$pattern" "$source" >/dev/null; then
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  fi
}

inertia=DASHI/Moonshine/Monster3BCentralCharacterInertiaExact.agda
probe=DASHI/Moonshine/MonsterOggNonaryProbeAuthorityExact.agda
pipeline=DASHI/Moonshine/Monster3BActualZetaPromotionPipelineExact.agda
split=DASHI/Moonshine/Monster3BMultiplicityTwelveSeventyEightRecognitionExact.agda
validation=DASHI/Moonshine/Monster3BCentralCharacterInertiaRound5Validation.agda
aggregate=DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
reference=Docs/support/reference/Monster3BCentralCharacterInertiaRound5.md

if [ ! -s "$reference" ]; then
  echo "missing or empty reference file: $reference" >&2
  exit 1
fi

require_pattern "$inertia" 'CentralInertia'
require_pattern "$inertia" 'inertiaActsWithinPhase'
require_pattern "$inertia" 'inverterSwapsPhase'
require_pattern "$inertia" 'ActualMonster3BPhaseResolvedSector'
require_pattern "$inertia" 'actualMonsterPhaseResolvedSectorConstructedIsFalse'
require_pattern "$probe" 'nonaryProbe'
require_pattern "$probe" 'allAboveThreeOggResiduesAreUnits'
require_pattern "$probe" 'complementUnitResidueExact'
require_pattern "$probe" 'plusThreeDoesNotTakeSevenToTwo'
require_pattern "$probe" 'proposedFractranOrderedPlusThreeImpossible'
require_pattern "$probe" 'reflectionPairSumsTo82'
require_pattern "$probe" 'NonaryProbeEquivariantPromotion'
require_pattern "$probe" 'genusZeroDerivedFromProbeIsFalse'
require_pattern "$probe" 'lerayProjectorDerivedFromFortyOneIsFalse'
require_pattern "$pipeline" 'ActualZetaPromotionPipeline'
require_pattern "$pipeline" 'chosenInertiaAction'
require_pattern "$pipeline" 'chosenOwnWeightProjectorCoefficient'
require_pattern "$pipeline" 'chosenWeylExponent'
require_pattern "$pipeline" 'actualPipelineInhabitedIsFalse'
require_pattern "$split" 'ninetyIsTwelvePlusSeventyEight'
require_pattern "$split" 'TwelveSeventyEightRecognition'
require_pattern "$split" 'twelveIntertwines'
require_pattern "$split" 'seventyEightIntertwines'
require_pattern "$split" 'actualTwoSidedDecompositionConstructedIsFalse'
require_pattern "$validation" 'uniformOrderedPlusThreeIsImpossible'
require_pattern "$validation" 'pipelineTransportsOwnWeightProjector'
require_pattern "$aggregate" 'Monster3BOrbifoldLocalModuleRound4'
require_pattern "$aggregate" 'Monster3BCentralCharacterInertiaRound5Validation'
require_pattern "$reference" 'the proposed ordered FRACTRAN map is not one uniform `+3` transform'
require_pattern "$reference" 'A genuine theorem now requires'

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Monster3BCentralCharacterInertiaRound5Validation.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
