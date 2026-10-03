#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': ['eval-involution', 'toIntegerSwapSign', 'toIntegerInvertWord'],
    'DASHI/Algebra/BalancedTernaryPositionalInjectiveExact.agda': ['evalIntegerCons', 'toIntegerInjective'],
    'DASHI/Algebra/BalancedTernaryRankReconstructionExact.agda': ['rankWord', 'unrankWord', 'unrankRankWord', 'rankUnrankWord'],
    'DASHI/Algebra/BalancedTernaryRankNegationExact.agda': ['rankInvertIsOpposite'],
    'DASHI/Algebra/BalancedTernaryCenteredReconstructionExact.agda': ['CenteredInteger', 'decodeEncodeCentered', 'encodeDecodeCentered', 'balancedTernaryCenteredBijection'],
    'DASHI/ComputerScience/TekumFixedWidthBalancedArithmeticExact.agda': ['negateWordIsInvertWord', 'tekumBalancedArithmetic', 'concreteAnchor', 'concreteAnchorNegationInvariant'],
    'DASHI/ComputerScience/TekumSourceWordDecodeExact.agda': ['integerToIntCodeRoundTrip', 'fractionIntCodeInteger', 'exponentIntCodeInteger', 'parseTekumWord'],
    'DASHI/ComputerScience/TekumSourceWordRoundTripExact.agda': ['rejoinPayloadCorrect', 'rejoinParsedAnchorPayloadCorrect', 'rejoinPayloadDeterminesSourcePayload', 'sourceParserImageIsLossless'],
    'DASHI/ComputerScience/TekumSourceNegationExact.agda': ['parseTekumWordNegation'],
    'DASHI/ComputerScience/TekumFractionRationalRangeExact.agda': ['fractionStrictHalfBound', 'canonicalFractionIsSignedDivision'],
    'DASHI/ComputerScience/TekumSignificandRangeExact.agda': ['significandStrictBand', 'nextExponentLowerEqualsCurrentUpper'],
    'DASHI/ComputerScience/TekumTriadicScaleExact.agda': ['integerSucc', 'triadicScale', 'triadicScalePositive', 'rawTriadicScaleSucc', 'triadicScaleSucc', 'intCodeTriadicScaleCanonical'],
    'DASHI/ComputerScience/TekumExponentBandExact.agda': [
        'bandLower', 'bandUpper', 'bandLowerPositive', 'adjacentBoundaryEquality',
        'InBand', 'adjacentBandsDisjoint', 'sameValueCannotOccupyAdjacentBands',
    ],
    'DASHI/ComputerScience/TekumParsedExactTriadicWeldExact.agda': [
        'exactPow3MatchesBalancedPow3', 'parsedExactBaseUnit',
        'parsedExactAdjustmentInteger', 'parsedExactScale', 'parsedExactUnsignedSignificandInteger',
    ],
    'DASHI/ComputerScience/TekumParsedExactRationalCoordinatesExact.agda': [
        'parsedSourceUnsignedNumerator', 'parsedExactNumeratorUsesSourceCoordinates',
        'parsedExactDenominatorUsesSourceCoordinates', 'parsedOrdinaryRationalUsesExactSourceCoordinates',
    ],
    'DASHI/ComputerScience/TekumWheelStateParityExact.agda': [
        'EvenWidth', 'OddWidth', 'pow3Mod4TwoStep', 'pow3Mod4Even', 'pow3Mod4Odd',
        'pow3Mod4OneImpliesEvenWidth', 'wheelQuarterIntegralityIffEvenWidth',
    ],
    'DASHI/ComputerScience/TekumExactTriadicSemanticsExact.agda': ['pow3NonZero', 'exactTriadicRationalUsesSignedDivision'],
    'DASHI/ComputerScience/TekumPadicDualCylinderNaturalityExact.agda': ['dualPrecisionTwoIsCylinderRefinementTwo'],
    'DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda': ['canonicalTekumVerifiedAssemblyBoundary'],
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

print('Tekum static regression: exact source rational coordinates, parsed triadic weld, general wheel parity, parser recovery, exponent/significand bands, source negation and p-adic naturality present.')
