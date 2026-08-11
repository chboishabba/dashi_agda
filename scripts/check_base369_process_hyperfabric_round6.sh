#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

sources=(
  DASHI/Foundations/Base369SignedMembershipExact.agda
  DASHI/Foundations/Base369LayeredAttractorAndCoarseFineExact.agda
  DASHI/Foundations/Base369AddressSymmetryAndBranchGeometryExact.agda
  DASHI/Foundations/Base369ProcessBranchAttractorExact.agda
  DASHI/Foundations/Base369ProcessHyperfabricRound6Validation.agda
  DASHI/EverythingBase369ProcessHyperfabricRound6.agda
)

for source in "${sources[@]}"; do
  test -s "$source" || { echo "missing or empty source: $source" >&2; exit 1; }
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
  grep -F "$pattern" "$source" >/dev/null || {
    echo "missing required marker '$pattern' in $source" >&2
    exit 1
  }
}

signed=DASHI/Foundations/Base369SignedMembershipExact.agda
layered=DASHI/Foundations/Base369LayeredAttractorAndCoarseFineExact.agda
symmetry=DASHI/Foundations/Base369AddressSymmetryAndBranchGeometryExact.agda
process=DASHI/Foundations/Base369ProcessBranchAttractorExact.agda
validation=DASHI/Foundations/Base369ProcessHyperfabricRound6Validation.agda
aggregate=DASHI/EverythingBase369ProcessHyperfabricRound6.agda
reference=Docs/support/reference/Base369ProcessHyperfabricRound6.md

require_pattern "$signed" 'SignedMembership'
require_pattern "$signed" 'memberOfInverse'
require_pattern "$signed" 'notMemberOfEither'
require_pattern "$signed" 'NominalActual'
require_pattern "$signed" 'ZeroKind'

require_pattern "$layered" 'Horizon3'
require_pattern "$layered" 'Depth6'
require_pattern "$layered" 'Depth9'
require_pattern "$layered" 'LayeredAttractor'
require_pattern "$layered" 'CoarseFine11'
require_pattern "$layered" 'CoarseWithNominalActual'
require_pattern "$layered" 'AddressedFibre'

require_pattern "$symmetry" 'OperatorEquivariance'
require_pattern "$symmetry" 'PropagationEquivariance'
require_pattern "$symmetry" 'TritPath'
require_pattern "$symmetry" 'OpenHoleTree'
require_pattern "$symmetry" 'ProvenanceDAG'
require_pattern "$symmetry" 'ConstrainedBraid'
require_pattern "$symmetry" 'StepStateSymmetry'

require_pattern "$process" 'ProcessBranch'
require_pattern "$process" 'GoalProcessState'
require_pattern "$process" 'FibredBranchValue'
require_pattern "$process" 'BranchSimilarity'
require_pattern "$process" 'EffectiveBranchOrbit'
require_pattern "$process" 'BeneficialBranchAddition'

require_pattern "$validation" 'booleanGoodCollapsesOutsideAndInverse₁'
require_pattern "$validation" 'localSuccessGlobalTrap'
require_pattern "$validation" 'projectDepth9ToImmediate'
require_pattern "$validation" 'sampleTritPath'
require_pattern "$validation" 'explorationAndCirculationShareZeroOrientation'
require_pattern "$aggregate" 'Base369ProcessHyperfabricRound6Validation'

test -s "$reference" || { echo "missing reference: $reference" >&2; exit 1; }
require_pattern "$reference" 'Signed membership rather than Boolean complement'
require_pattern "$reference" 'Coarse/fine 11'
require_pattern "$reference" 'Tree, DAG, and braid geometry'

scripts/run_agda29_parallel_check.sh \
  DASHI/Foundations/Base369ProcessHyperfabricRound6Validation.agda \
  DASHI/EverythingBase369ProcessHyperfabricRound6.agda \
  DASHI/EverythingMonster3BCentralCharacterInertiaRound5.agda
