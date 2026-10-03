#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': [
        'eval-involution',
        'threeTritExtremalPositiveWeight',
    ],
    'DASHI/Algebra/BalancedTernaryA003462BridgeExact.agda': [
        'threePositiveTritEvaluationMatchesA003462Magnitude',
    ],
    'DASHI/Algebra/BalancedTernaryFiniteCarrierExact.agda': [
        'finTritRoundTrip',
        'tritFinRoundTrip',
        'fromToFin3',
        'toFromFin3',
        'canonicalFin3VectorEnumerationLength',
    ],
    'DASHI/Algebra/BalancedTernaryPositionalInjectiveExact.agda': [
        'digitInteger',
        'evalIntegerCons',
        'balancedRemainderDistinct',
        'toIntegerInjective',
        'oneTritNegativeInteger',
        'oneTritZeroInteger',
        'oneTritPositiveInteger',
        'twoTritNegativePositiveInteger',
        'twoTritZeroPositiveInteger',
        'twoTritPositivePositiveInteger',
    ],
    'DASHI/Foundations/RadixScaledExactFormat.agda': [
        'bf16ScaledExactFormat',
        'TaperedWidthAllocation',
    ],
    'DASHI/Codec/TriadicPAdicCylinderExact.agda': [
        'canonicalTriadicCylinderSystem',
        'projectCompatible',
    ],
    'DASHI/ComputerScience/TekumExactTriadicSemanticsExact.agda': [
        'ordinaryExactTriadic',
        'ordinaryRational',
        'applySignFlip',
        'flipExactTriadicDenominatorInvariant',
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
        'tekumAndPadicDepthOneDiffer',
    ],
    'DASHI/ComputerScience/TekumPadicDualChartExact.agda': [
        'dualChartInvolutive',
        'tekumPrecisionConjugatesToDual',
        'dualTwoStepComposition',
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
    'DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda': [
        'canonicalTekumVerifiedAssemblyBoundary',
        'canonicalRationalOrdinaryDecoderPresent',
        'finiteTritPowerThreeCardinalityPaid',
        'reversalDualChartPresent',
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

print('Tekum static regression: positional injectivity, rational semantics, finite 3^n carrier, dual p-adic chart, ternary-machine, ABI and SSP/FRACTRAN welds present.')
