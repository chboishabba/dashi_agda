#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"

required_files=(
  DASHI/Core/IntegrationConsumerDescentOrderExact.agda
  DASHI/Biology/IIT4FiniteCausalStructureExact.agda
  DASHI/Biology/IITXORGridAdversarialExact.agda
  DASHI/Biology/IITCyclotomicFourierObserverExact.agda
  DASHI/Biology/IITBalancedTernary369HierarchyExact.agda
  DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda
  DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda
  DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda
  DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda
  DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda
  DASHI/Biology/IITPhiIntegrationEverything.agda
  DASHI/EverythingIITPhiIntegrationMaxCut.agda
)

for path in "${required_files[@]}"; do
  [[ -f "$ROOT/$path" ]] || { echo "missing IIT max-cut file: $path" >&2; exit 1; }
done

require() {
  local file="$1"
  local needle="$2"
  grep -Fq "$needle" "$ROOT/$file" || {
    echo "missing contract '$needle' in $file" >&2
    exit 1
  }
}

require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiSystem : SystemPartition system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiDistinction : CausalDistinction system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiRelation : CausalRelation system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'bigPhi :'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'historicalCounterexampleVersionBoundary'

require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'orderFailureBlocksPreservation'
require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'nonDescentBlocksScoreFactorization'
require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'structuralScoreDoesNotSelfPromote'

require DASHI/Biology/IITXORGridAdversarialExact.agda 'parityCannotFactorLeftBit'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'lineAndSquareCutCountsDiffer'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'graphCutIsNotSilentlyPromotedToIIT4'

require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'fourier27IdentitySufficient'
require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'firstCoefficientCannotRecoverTail'

require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'rank1OrbitCannotRecoverSignedIdentity'
require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'raw369Counts'
require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'stageFiveResidualSurvivesVisibleFallback'

require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'vertexPartitionNotDefinitionallySectionPartition'
require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'compatibleSection : Hyperfabric.GlobalSection fabric'

require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'integrationScoreDoesNotCreateBiologicalIdentity'
require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'accessAndIITRemainSeparateTheories'

require DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda 'normLosesC3Phase'
require DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda 'normZeroStillSeparatesZero'

require DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda 'singleCoefficientCannotRecoverNextCoefficient'
require DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda 'finitePackagingIsNotAnalyticContinuation'

require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Analysis.IITZetaGeneratingBoundaryExact'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationEverything'

echo 'IIT phi integration max-cut static contract: PASS'
