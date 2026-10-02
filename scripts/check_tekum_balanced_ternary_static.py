#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': [
        'eval-involution',
        'threeTritExtremalPositiveWeight',
    ],
    'DASHI/Foundations/RadixScaledExactFormat.agda': [
        'bf16ScaledExactFormat',
        'TaperedWidthAllocation',
    ],
    'DASHI/Codec/TriadicPAdicCylinderExact.agda': [
        'canonicalTriadicCylinderSystem',
        'projectCompatible',
    ],
    'DASHI/ComputerScience/TekumRegimeExponentExact.agda': [
        'decodeEncodeRegime',
        'outerPositiveBiasIs244',
    ],
    'DASHI/ComputerScience/TekumFloatingPointStructuralBridgeExact.agda': [
        'tekumOrientationRoleMatchesBF16SignRole',
        'tekumScaleRoleMatchesBF16ExponentRole',
        'tekumRefinementRoleMatchesBF16FractionRole',
        'centralRegimeAtWidth8',
        'outerRegimeAtWidth8',
    ],
    'DASHI/ComputerScience/TekumTriadicPAdicKernelBridgeExact.agda': [
        'fromToKernel',
        'toFromKernel',
        'truncateCommutesWithCarrierWeld',
        'kernelTwoStepProjectionComposes',
    ],
    'DASHI/ComputerScience/TekumPadicOrientationBoundaryExact.agda': [
        'tekumSampleKeepsHighTrit',
        'padicSampleDepthOne',
        'tekumAndPadicDepthOneDiffer',
    ],
    'DASHI/ComputerScience/TekumTernaryStoredProgramExecutionExact.agda': [
        'regimeStorageRoundTrip',
        'ternaryExecutionMatchesNative',
        'positiveOuterRegimeEchoesFourteen',
    ],
    'DASHI/ComputerScience/TekumTriadicABIBackendBoundaryExact.agda': [
        'Pack5Obligation',
        'canonicalTekumBackendBoundary',
    ],
    'DASHI/ComputerScience/TekumSSPFRACTRANBridgeExact.agda': [
        'positionedReopenExact',
        'positionedCodeSeparatesTekumDigit',
        'negativeUnitAtOneCompilesToThreeInversePrimes',
    ],
    'DASHI/ComputerScience/TekumFieldRoleSSPAtlasExact.agda': [
        'canonicalRadixThreeAtlas',
        'separatedRoleAtlas',
    ],
    'DASHI/ComputerScience/TekumPrecisionCompositionExact.agda': [
        'truncateTwoTwiceEqualsFour',
    ],
    'DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda': [
        'canonicalTekumVerifiedAssemblyBoundary',
        'executablePadicCylinderSystemPresent',
        'tekumTruncationEqualsPadicCylinderWithoutReversal',
        'concreteTernaryStoredProgramExecutionPresent',
    ],
}

for rel, needles in required.items():
    path = ROOT / rel
    if not path.exists():
        raise SystemExit(f'missing required Tekum owner: {rel}')
    text = path.read_text(encoding='utf-8')
    for needle in needles:
        if needle not in text:
            raise SystemExit(f'missing {needle} in {rel}')
    for bad in ('{!!}', 'postulate', 'TERMINATE', 'TODO_PLACEHOLDER'):
        if bad in text:
            raise SystemExit(f'forbidden marker {bad!r} in {rel}')

print('Tekum static regression: floating, p-adic cylinder/orientation, ternary-machine, ABI and SSP/FRACTRAN welds present.')
