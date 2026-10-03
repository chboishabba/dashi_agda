#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': [
        'eval-involution', 'threeTritExtremalPositiveWeight',
        'toIntegerSwapSign', 'toIntegerInvertWord',
    ],
    'DASHI/Algebra/BalancedTernaryA003462BridgeExact.agda': ['threePositiveTritEvaluationMatchesA003462Magnitude'],
    'DASHI/Algebra/BalancedTernaryFiniteCarrierExact.agda': ['finTritRoundTrip', 'tritFinRoundTrip', 'fromToFin3', 'toFromFin3', 'canonicalFin3VectorEnumerationLength'],
    'DASHI/Algebra/BalancedTernaryPositionalInjectiveExact.agda': [
        'digitInteger', 'evalIntegerCons', 'balancedRemainderDistinct', 'toIntegerInjective',
        'oneTritNegativeInteger', 'oneTritZeroInteger', 'oneTritPositiveInteger',
        'twoTritNegativePositiveInteger', 'twoTritZeroPositiveInteger', 'twoTritPositivePositiveInteger',
    ],
    'DASHI/Algebra/BalancedTernaryRankReconstructionExact.agda': [
        'rankWord', 'unrankWord', 'unrankRankWord', 'rankUnrankWord',
        'rankToNatCode', 'natCodeStrictBound', 'pow3RightMatchesPow3',
    ],
    'DASHI/Algebra/BalancedTernaryRankNegationExact.agda': [
        'digitNatInvertComplement', 'natCodeInvertComplement', 'rankInvertIsOpposite',
    ],
    'DASHI/Algebra/BalancedTernaryCenteredReconstructionExact.agda': [
        'twiceCenterPlusOne', 'CenteredInteger', 'centeredValue',
        'encodeCentered', 'decodeCentered', 'decodeEncodeCentered', 'encodeDecodeCentered',
        'centeredValueWithinRange', 'centeredValueEncode', 'balancedTernaryCenteredBijection',
    ],
    'DASHI/ComputerScience/TekumFixedWidthBalancedArithmeticExact.agda': [
        'wrapRank', 'negateCentered', 'addCentered', 'subtractCentered', 'modulusCentered',
        'negateWord', 'negateWordIsInvertWord', 'addWord', 'subtractWord', 'modulusWord', 'allPositiveWord',
        'modulusNegateWord', 'tekumBalancedArithmetic', 'concreteAnchor',
        'concreteAnchorNegationInvariant', 'oneTritPositivePlusPositiveWrapsNegative',
    ],
    'DASHI/ComputerScience/TekumDefinition5ConsistencyExact.agda': [
        'sourceOverflowAdjustment', 'definition5WidthOnePositiveOverflow',
        'carryDiscardWidthOnePositiveOverflow', 'definition5DiffersFromCarryDiscardAtWidthOne',
        'anchorSubtractionNeverNeedsPositiveOverflow', 'sourceEquationAndCarryDescriptionSeparated',
    ],
    'DASHI/ComputerScience/TekumSourceWordDecodeExact.agda': [
        'signOfWord', 'ParsedPayload', 'parsePayload', 'anchorMSB', 'parseAnchorMSB', 'parseOrdinaryAnchor',
        'integerToIntCode', 'exponentIntCode', 'fractionIntCode', 'ordinaryFromParsed',
        'parseTekumWord', 'decodeNormalWidthTekumWord', 'normalWidthParserUsesSourceFieldOrder',
    ],
    'DASHI/ComputerScience/TekumSourceWordRoundTripExact.agda': [
        'rejoinPayload', 'rejoinPayloadCorrect', 'regimePrefixMSB', 'rejoinAnchorMSB',
        'rejoinParsedAnchorMSB', 'rejoinParsedAnchorPayloadCorrect', 'sourceParserImageIsLossless',
    ],
    'DASHI/ComputerScience/TekumSourceNegationExact.agda': [
        'signOfIntegerNegation', 'signOfInvertWord', 'signOfNegateWord',
        'anchorMSBNegationInvariant', 'parseOrdinaryAnchorNegationInvariant',
        'ordinaryParsedNegation', 'parseTekumWordNegation',
    ],
    'DASHI/ComputerScience/TekumFractionRangeExact.agda': [
        'fractionIntegerLower', 'fractionIntegerUpper', 'fractionIntegerRange',
        'twiceCenterPlusOneIsPowerThree', 'twiceCenterStrictlyBelowPowerThree',
    ],
    'DASHI/Foundations/RadixScaledExactFormat.agda': ['bf16ScaledExactFormat', 'TaperedWidthAllocation'],
    'DASHI/Codec/TriadicPAdicCylinderExact.agda': ['canonicalTriadicCylinderSystem', 'projectCompatible'],
    'DASHI/ComputerScience/TekumExactTriadicSemanticsExact.agda': ['ordinaryExactTriadic', 'ordinaryRational', 'applySignFlip', 'flipExactTriadicDenominatorInvariant'],
    'DASHI/ComputerScience/TekumRegimeExponentExact.agda': ['decodeEncodeRegime', 'outerPositiveBiasIs244'],
    'DASHI/ComputerScience/TekumFloatingPointStructuralBridgeExact.agda': [
        'tekumOrientationRoleMatchesBF16SignRole', 'tekumScaleRoleMatchesBF16ExponentRole',
        'tekumRefinementRoleMatchesBF16FractionRole', 'centralRegimeAtWidth8', 'outerRegimeAtWidth8',
    ],
    'DASHI/ComputerScience/TekumTriadicPAdicKernelBridgeExact.agda': ['fromToKernel', 'toFromKernel', 'truncateCommutesWithCarrierWeld', 'kernelTwoStepProjectionComposes'],
    'DASHI/ComputerScience/TekumPadicOrientationBoundaryExact.agda': ['tekumAndPadicDepthOneDiffer'],
    'DASHI/ComputerScience/TekumPadicDualChartExact.agda': ['dualChartInvolutive', 'tekumPrecisionConjugatesToDual', 'dualTwoStepComposition'],
    'DASHI/ComputerScience/TekumPadicDualCylinderNaturalityExact.agda': ['dualDropOneIsInit', 'toKernelInitNaturality', 'dualPrecisionTwoIsCylinderRefinementTwo', 'finiteNaturalityOnly'],
    'DASHI/ComputerScience/TekumTernaryStoredProgramExecutionExact.agda': ['regimeStorageRoundTrip', 'ternaryExecutionMatchesNative', 'positiveOuterRegimeEchoesFourteen'],
    'DASHI/ComputerScience/TekumTriadicABIBackendBoundaryExact.agda': ['Pack5Obligation', 'canonicalTekumBackendBoundary'],
    'DASHI/ComputerScience/TekumSSPFRACTRANBridgeExact.agda': ['positionedReopenExact', 'positionedCodeSeparatesTekumDigit', 'negativeUnitAtOneCompilesToThreeInversePrimes'],
    'DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda': ['canonicalTekumVerifiedAssemblyBoundary', 'canonicalRationalOrdinaryDecoderPresent', 'finiteTritPowerThreeCardinalityPaid', 'reversalDualChartPresent'],
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

print('Tekum static regression: exact fraction range, source-level negation, parser roundtrip, centered backend, rational semantics, p-adic naturality and hardware boundaries present.')
