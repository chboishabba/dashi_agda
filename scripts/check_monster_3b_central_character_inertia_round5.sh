#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

bash scripts/check_monster_3b_orbifold_local_module_round4.sh

sources=(
  DASHI/Moonshine/Monster3BCentralCharacterInertiaExact.agda
  DASHI/Moonshine/MonsterOggNonaryProbeAuthorityExact.agda
  DASHI/Moonshine/MonsterOggNonarySevenSevenOneEquivalenceExact.agda
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
partition=DASHI/Moonshine/MonsterOggNonarySevenSevenOneEquivalenceExact.agda
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

# Complete nonary address and closed-residue exclusion.
require_pattern "$probe" 'nonaryProbe'
require_pattern "$probe" 'allOggFineResiduesAreOpen'
require_pattern "$probe" 'allOggFineResiduesAvoidZero'
require_pattern "$probe" 'allOggFineResiduesAvoidSix'
require_pattern "$probe" 'allAboveThreeOggResiduesAreUnits'

# Three complement modes x two orientations.
require_pattern "$probe" 'complementUnitResidueExact'
require_pattern "$probe" 'complementUnitResidueInvolutive'
require_pattern "$probe" 'UnitComplementMode'
require_pattern "$probe" 'UnitOrientation'
require_pattern "$probe" 'complementPreservesUnitMode'
require_pattern "$probe" 'complementFlipsUnitOrientation'

# Sorted-list signature is not the actual FRACTRAN relation.
require_pattern "$probe" 'sortedEarningStartResidues'
require_pattern "$probe" 'sortedEarningEndResidues'
require_pattern "$probe" 'plusThreeDoesNotTakeSevenToTwo'
require_pattern "$probe" 'proposedFractranOrderedPlusThreeImpossible'
require_pattern "$probe" 'ActualFractranReplacement'
require_pattern "$probe" 'replace23By47'
require_pattern "$probe" 'replace7By59'
require_pattern "$probe" 'replace11By71'
require_pattern "$probe" 'actualFractranReplacementIsNotPlusThree'
require_pattern "$probe" 'actualFractranEarningChain'
require_pattern "$probe" 'earnedPrimeProductIs196883'
require_pattern "$probe" 'earnedPrimeProductPlusOneIs196884'

# Depth-two nonary and T7A normalization mathematics.
require_pattern "$probe" 'seventyOnePlusTenCompletesEightyOne'
require_pattern "$probe" 'fortyOneIsPointedMidpointOfEightyOne'
require_pattern "$probe" 'reflectionPairSumsTo82'
require_pattern "$probe" 'unnormalizedSevenAConstantIsTen'
require_pattern "$probe" 'normalizedSevenAConstantIsZero'
require_pattern "$probe" 'sevenANormalizationRemovesTen'
require_pattern "$probe" 'sevenAFirstPositiveCoefficientIs51'
require_pattern "$probe" 'sevenASecondPositiveCoefficientIs204'
require_pattern "$probe" 'seventyOneDeficitMatchesUnnormalizedSevenAConstant'

# Semantic 7+7+1 data and exact carrier equivalence.
require_pattern "$probe" 'MirrorA7Lane'
require_pattern "$probe" 'MirrorB7Lane'
require_pattern "$probe" 'Sign1Lane'
require_pattern "$probe" 'mirrorA7CountIsSeven'
require_pattern "$probe" 'mirrorB7CountIsSeven'
require_pattern "$probe" 'sign1CountIsOne'
require_pattern "$probe" 'semanticSevenSevenOneCountIsFifteen'
require_pattern "$probe" 'mirrorA7BelowSeventhCoarseSheet'
require_pattern "$probe" 'mirrorB7BelowSeventhCoarseSheet'
require_pattern "$probe" 'sign1CoarseSheetIsSeven'
require_pattern "$probe" 'sign1FineResidueIsEight'
require_pattern "$partition" 'SemanticSevenSevenOneLane'
require_pattern "$partition" 'classifyOggLane'
require_pattern "$partition" 'forgetSevenSevenOneLane'
require_pattern "$partition" 'forgetAfterClassify'
require_pattern "$partition" 'classifyAfterForget'
require_pattern "$partition" 'SevenSevenOneCarrierEquivalence'
require_pattern "$partition" 'canonicalSevenSevenOneCarrierEquivalence'
require_pattern "$partition" 'coarseSheetSevenUniquelyIdentifiesP71'
require_pattern "$partition" 'p71IsClassifiedAsSign1'

# Explicit promotion boundary.
require_pattern "$probe" 'NonaryProbeEquivariantPromotion'
require_pattern "$probe" 'actualForwardTransitionConstructedIsFalse'
require_pattern "$probe" 'actualMonsterEquivariantProbeConstructedIsFalse'
require_pattern "$probe" 'normalizedSevenAConstantTermIsTenIsFalse'
require_pattern "$probe" 'rawSevenAConstantIsMonsterSurvivingMassIsFalse'
require_pattern "$probe" 'genusZeroDerivedFromProbeIsFalse'
require_pattern "$probe" 'genusZeroEquivalentToAcyclicCascadeIsFalse'
require_pattern "$probe" 'lerayProjectorDerivedFromFortyOneIsFalse'
require_pattern "$probe" 'sevenSevenOneIsMonsterModuleDecompositionIsFalse'
require_pattern "$probe" 'clayYangMillsPromotedIsFalse'

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

# Cumulative proof surface.
require_pattern "$validation" 'allOggResiduesExcludeZero'
require_pattern "$validation" 'allOggResiduesExcludeSix'
require_pattern "$validation" 'unitComplementReversesOrientation'
require_pattern "$validation" 'uniformOrderedPlusThreeIsImpossible'
require_pattern "$validation" 'actualReplacementPlusThreeIsImpossible'
require_pattern "$validation" 'actualEarningChainReaches196883'
require_pattern "$validation" 'earnedProductAdjoinsOneTo196884'
require_pattern "$validation" 'fortyOneIsPointedMidpoint'
require_pattern "$validation" 'rawSevenAConstantIsTen'
require_pattern "$validation" 'normalizedSevenAConstantVanishes'
require_pattern "$validation" 'sevenANormalizationOffsetIsTen'
require_pattern "$validation" 'rawSevenAOffsetCompletes196874To196884'
require_pattern "$validation" 'sevenSevenOneReconstructsFifteen'
require_pattern "$validation" 'sevenSevenOneClassificationForgetsExactly'
require_pattern "$validation" 'sevenSevenOneForgettingClassifiesExactly'
require_pattern "$validation" 'observerLaneOccupiesCoarseSheetSeven'
require_pattern "$validation" 'coarseSheetSevenUniquelySelectsObserver'
require_pattern "$validation" 'pipelineTransportsOwnWeightProjector'
require_pattern "$aggregate" 'Monster3BOrbifoldLocalModuleRound4'
require_pattern "$aggregate" 'MonsterOggNonarySevenSevenOneEquivalenceExact'
require_pattern "$aggregate" 'Monster3BCentralCharacterInertiaRound5Validation'

require_pattern "$reference" 'actual FRACTRAN replacement relation'
require_pattern "$reference" 'normalized `7A` Hauptmodul has constant `0`'
require_pattern "$reference" 'No transition relation is constructed'
require_pattern "$reference" 'two-sided finite equivalence'
require_pattern "$reference" '196874 + 10 = 196884'
require_pattern "$reference" 'A genuine theorem now requires'

scripts/run_agda29_parallel_check.sh \
  DASHI/Moonshine/Monster3BCentralCharacterInertiaRound5Validation.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
