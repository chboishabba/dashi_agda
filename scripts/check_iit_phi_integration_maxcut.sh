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
  DASHI/Biology/IITCausalPantsFibreGluingExact.agda
  DASHI/Biology/IITCausalPantsOrientationBoundaryExact.agda
  DASHI/Biology/IITPointedTernary27FaceGluingExact.agda
  DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda
  DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda
  DASHI/Biology/IITPointedTernary27Origin26Exact.agda
  DASHI/Biology/IITPointedTernary27Recentered26Exact.agda
  DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda
  DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda
  DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda
  DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda
  DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda
  DASHI/Biology/IITPhiIntegrationEverything.agda
  DASHI/EverythingIITPhiIntegrationMaxCut.agda
  scripts/iit_pants_fabric_matched_gate_scan.py
  scripts/data/outputs/iit_pants_fabric_matched_gate_scan_20261014.json
)
for path in "${required_files[@]}"; do
  [[ -f "$ROOT/$path" ]] || { echo "missing IIT max-cut file: $path" >&2; exit 1; }
done

require() { grep -Fq "$2" "$ROOT/$1" || { echo "missing contract '$2' in $1" >&2; exit 1; }; }
reject() { ! grep -Fq "$2" "$ROOT/$1" || { echo "forbidden contract '$2' in $1" >&2; exit 1; }; }

# IIT 4 finite spine and exact XOR fixture.
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiSystem : SystemPartition system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiDistinction : CausalDistinction system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'phiRelation : CausalRelation system → Score'
require DASHI/Biology/IIT4FiniteCausalStructureExact.agda 'bigPhi :'
require DASHI/Biology/IIT4FiniteProbabilityRepertoireExact.agda 'effectConditionalFraction'
require DASHI/Biology/IIT4SystemPhiInputExact.agda 'MinimumPartitionWitness'
require DASHI/Biology/IIT4SymbolicScalarBackendExact.agda 'symbolicSystemPhiAtPartition'
require DASHI/Biology/IITXORGridAdversarialExact.agda 'xorTwoBitFiniteCausalSystem : IIT4.FiniteCausalSystem'
require DASHI/Biology/IITXORProbabilityReceiptExact.agda 'unconstrained11IsOneQuarter'
require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'partitionedEffect10to11IsHalf'
require DASHI/Biology/IITXOREffectCutReceiptExact.agda 'symbolicIntegratedEffect10to11IsExactEquationTree'

# Generic observer/descent and cyclotomic/369 surfaces.
require DASHI/Core/IntegrationConsumerDescentOrderExact.agda 'nonDescentBlocksScoreFactorization'
require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'fourier27IdentitySufficient'
require DASHI/Biology/IITCyclotomicFourierObserverExact.agda 'firstCoefficientCannotRecoverTail'
require DASHI/Biology/IITBalancedTernary369HierarchyExact.agda 'rank1OrbitCannotRecoverSignedIdentity'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'canonicalPantsHasThreeOutputs'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'nineSheetPantsRoundTrip'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'voxel27PantsRoundTrip'
require DASHI/Biology/IIT369PantsGluingBridgeExact.agda 'sameNineStatesDoNotForceSameAlgebra'

# Causal pants: gluing/transport and local algebra are independent coordinates.
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'record LocalSynthesisCell'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'record OutputInputGluing'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'record TwoSourceInputGluing'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'evaluateGluedCell'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'sameFabricDifferentLocalAlgebraChangesOutput'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'triXorOnSameFabric'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'record ClosedTwoStepCircuit'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'gluingIsNotGate'
require DASHI/Biology/IITCausalPantsFibreGluingExact.agda 'partitionDoesNotRewriteGate'
require DASHI/Biology/IITCausalPantsOrientationBoundaryExact.agda 'branchingDoesNotManufactureSynthesisOrientation'
require DASHI/Biology/IITCausalPantsOrientationBoundaryExact.agda 'causalCellStillOwnsTwoInputs'

# Matched fixed-fabric scanner/receipt.
require scripts/iit_pants_fabric_matched_gate_scan.py 'A[t+1] = C[t]'
require scripts/iit_pants_fabric_matched_gate_scan.py 'C[t+1] = mu(A[t], B[t])'
require scripts/iit_pants_fabric_matched_gate_scan.py 'binary XOR'
require scripts/iit_pants_fabric_matched_gate_scan.py 'binary OR'
require scripts/iit_pants_fabric_matched_gate_scan.py 'binary AND'
require scripts/iit_pants_fabric_matched_gate_scan.py 'ternary triXor'
require scripts/data/outputs/iit_pants_fabric_matched_gate_scan_20261014.json '"zero_phi_states": 6'
require scripts/data/outputs/iit_pants_fabric_matched_gate_scan_20261014.json '"min_phi_s_bits": 3.169925001442312'
require scripts/data/outputs/iit_pants_fabric_matched_gate_scan_20261014.json 'fixed recurrent gluing topology is not sufficient to determine system phi_s'

# Pointed 27 = selected cubie + complement / compatible face gluing.
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'oneSelectedPlusTwentySixRemainingIsTwentySeven'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'originNotOnOuterFace'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'outerFaceSheetIsOnePlusEight'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'record PairwiseActiveFaceGluing'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'selectedCornerCocycle'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'recognizedZetaFaceGluing'
require DASHI/Biology/IITPointedTernary27FaceGluingExact.agda 'faceGluingDoesNotSelfPromoteToPhi'

# Three selected cubies still do not determine the irreducible triadic face.
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'sameSelectedCubies'
require DASHI/Biology/IITPointedTernary27TriadicNonDescentExact.agda 'selectedCubiesDoNotDetermineTriadicFace'

# Exact signed 27 <-> C3^3 <-> explicit Fourier cell/character index.
require DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda 'pointCell27RoundTrip'
require DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda 'cell27PointRoundTrip'
require DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda 'activeCharacterIndex'
require DASHI/Biology/IITPointedTernary27CyclotomicCellExact.agda 'cyclicAndGeometricAdjacencyRemainDistinct'

# Exact SAME-CARRIER 27 = origin + explicit NonOrigin26 decomposition.
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'nonActiveConstructorCountIsTwentySix'
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'nonActiveCubieIsNotOrigin'
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'originPlus26FromAfterTo'
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'originPlus26ToAfterFrom'
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'originMapsToDistinguishedScalar'
require DASHI/Biology/IITPointedTernary27Origin26Exact.agda 'origin26DoesNotSelfPromoteToPhi'

# Transport that 26-complement to every arbitrary selected cubie through C3^3.
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recenterSelectedCubieIsOrigin'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recenteredNonActiveNeverHitsSelected'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recenteredNonActiveInjective'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'canonicalArbitraryPointedComplement26'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recentringDoesNotManufactureGeometricSymmetry'
require DASHI/Biology/IITPointedTernary27Recentered26Exact.agda 'recentringDoesNotManufactureFaceSymmetry'

# Remaining cross-domain firewalls.
require DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda 'vertexPartitionNotDefinitionallySectionPartition'
require DASHI/Reasoning/IITBrainMaleCNSConsumerBoundaryExact.agda 'integrationScoreDoesNotCreateBiologicalIdentity'
require DASHI/Moonshine/IITMonsterInvariantBoundaryExact.agda 'normLosesC3Phase'
require DASHI/Analysis/IITZetaGeneratingBoundaryExact.agda 'finitePackagingIsNotAnalyticContinuation'

# Rollup must be acyclic and validation must sit outside production.
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITCausalPantsFibreGluingExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITCausalPantsOrientationBoundaryExact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPointedTernary27Origin26Exact'
require DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPointedTernary27Recentered26Exact'
reject DASHI/Biology/IITPhiIntegrationEverything.agda 'import DASHI.Biology.IITPhiIntegrationMaxCutValidation'
require DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda 'import DASHI.Biology.IITPhiIntegrationEverything'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationEverything'
require DASHI/EverythingIITPhiIntegrationMaxCut.agda 'import DASHI.Biology.IITPhiIntegrationMaxCutValidation'

echo 'IIT phi integration max-cut static contract: PASS'
