#!/usr/bin/env bash
set -euo pipefail

ROOT="${DASHI_REPO_ROOT:-$(cd "$(dirname "$0")/.." && pwd)}"

required_files=(
  DASHI/Core/IntegrationConsumerDescentOrderExact.agda
  DASHI/Biology/IIT4FiniteCausalStructureExact.agda
  DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda
  DASHI/Biology/IIT4SystemPhiInputExact.agda
  DASHI/Biology/IIT4SymbolicScalarBackendExact.agda
  DASHI/Biology/IITXORGridAdversarialExact.agda
  DASHI/Biology/IITXORProbabilityReceiptExact.agda
  DASHI/Biology/IITXOREffectCutReceiptExact.agda
  DASHI/Biology/IITCyclotomicFourierObserverExact.agda
  DASHI/Biology/IITBalancedTernary369HierarchyExact.agda
  DASHI/Biology/IIT369PantsGluingBridgeExact.agda
  DASHI/Biology/IITPointedTernary27FaceGluingExact.agda
  DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda
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

require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'data CutDirection'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'record DirectedPart'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'affectedConnectionCount : Nat'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiSystem : SystemPartition system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiDistinction : CausalDistinction system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiRelation : CausalRelation system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'bigPhi :'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'historicalCounterexampleVersionBoundary'

require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'effectConditionalFraction'
require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'unconstrainedEffectFraction'
require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'FiniteCauseRepertoire'
require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'PartitionedProbability'
require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'finiteFractionsDoNotManufactureLogs'

require DASHI/Biology/IIT4SystemPhiInputExact.agda 'integratedSideScore'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'systemPhiAtPartition'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'normalizedSystemPhiAtPartition'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'MinimumPartitionWitness'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'reusesCanonicalDirectionalPartition'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'normalizerIsNotPhiByDefinition'

require DASHI/Biology/IIT4SymbolicScalarBackendExact.agda 'data SymbolicScore'
require DASHI/Biology/IIT4SymbolicScalarBackendExact.agda 'symbolicSystemPhiAtPartition'
require DASHI/Biology/IIT4SymbolicScalarBackendExact.agda 'symbolicDoesNotPretendToEvaluateLog'

require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'orderFailureBlocksPreservation'
require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'nonDescentBlocksScoreFactorization'
require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'structuralScoreDoesNotSelfPromote'

require DASHI/Biology/IITXORGridAdversarialExact.agda 'xorTwoBitFiniteCausalSystem : IIT4.FiniteCausalSystem'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'xorDeterministicStepReceipt'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'parityCannotFactorLeftBit'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'lineAndSquareCutCountsDiffer'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'graphCutIsNotSilentlyPromotedToIIT4'

require DASHI/Biology/IITXORProbabilityReceiptExact.agda 'totalTransitionWeightIsFour'
require DASHI/Biology/IITXORProbabilityReceiptExact.agda 'conditional10to11IsCertain'
require DASHI/Biology/IITXORProbabilityReceiptExact.agda 'unconstrained11IsOneQuarter'
require DASHI/Biology/IITXORProbabilityReceiptExact.agda 'unpartitionedProbabilitiesDoNotManufacturePhi'

require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'oneWayXorPartition'
require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'causalMarginalizedSupportCountIsOne'
require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'partitionedEffect10to11IsHalf'
require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'symbolicIntegratedEffect10to11IsExactEquationTree'

require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'fourier27IdentitySufficient'
require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'firstCoefficientCannotRecoverTail'

require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'rank1OrbitCannotRecoverSignedIdentity'
require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'raw369Counts'
require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'stageFiveResidualSurvivesVisibleFallback'

require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'canonicalPantsHasThreeOutputs'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'nineSheetPantsRoundTrip'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'voxel27PantsRoundTrip'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'sameNineStatesDoNotForceSameAlgebra'

require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'oneSelectedPlusTwentySixRemainingIsTwentySeven'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'canonicalNoncentralCountIsTwentySix'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'originNotOnOuterFace'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'outerFaceSheetIsOnePlusEight'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'record PairwiseActiveFaceGluing'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'selectedCornerCocycle'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'threeActiveCubieChoiceCountIsHyperformCount'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'recognizedZetaFaceGluing'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'pairwiseStructuredBoundaryDoesNotDetermineTriadicFace'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'faceGluingDoesNotSelfPromoteToPhi'

require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'record ThreeSelectedCubies'
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'sameSelectedCubies'
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'selectedCubiesDoNotDetermineTriadicFace'
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'selectedCubiesDoNotSelfPromoteToGluingClass'

require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'vertexPartitionNotDefinitionallySectionPartition'
require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'compatibleSection : Hyperfabric.GlobalSection fabric'

require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'integrationScoreDoesNotCreateBiologicalIdentity'
require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'accessAndIITRemainSeparateTheories'

require DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda 'normLosesC3Phase'
require DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda 'normZeroStillSeparatesZero'

require DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda 'singleCoefficientCannotRecoverNextCoefficient'
require DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda 'finitePackagingIsNotAnalyticContinuation'

require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IIT4SymbolicScalarBackendExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITXOREffectCutReceiptExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IIT369PantsGluingBridgeExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPointedTernary27FaceGluingExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPointedTernary27TriadicNonDescentExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Analysis.IITZetaGeneratingBoundaryExact'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationEverything'

echo 'IIT phi integration max-cut static contract: PASS'
