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
    'DASHI/ComputerScience/TekumFractionInjectiveExact.agda': ['canonicalFractionEqualityToRaw', 'fractionNumeratorEquality', 'canonicalFractionInjective'],
    'DASHI/ComputerScience/TekumIntegerSuccessorGapExact.agda': ['advancePositive', 'advanceCommuteSucc', 'advanceNegativeToZero', 'advanceNegativeGap', 'integerLessHasPositiveAdvance'],
    'DASHI/ComputerScience/TekumRegimeExponentIntervalExact.agda': [
        'regimeLower', 'regimeUpper', 'parsedExponentRange', 'RegimeStep',
        'adjacentRegimeBoundary', 'stepRegimeIntervalsOrdered', 'regimeIntervalNonempty',
    ],
    'DASHI/ComputerScience/TekumSignificandRangeExact.agda': ['significandStrictBand', 'nextExponentLowerEqualsCurrentUpper'],
    'DASHI/ComputerScience/TekumTriadicScaleExact.agda': ['integerSucc', 'triadicScale', 'triadicScalePositive', 'rawTriadicScaleSucc', 'triadicScaleSucc', 'intCodeTriadicScaleCanonical'],
    'DASHI/ComputerScience/TekumExponentBandExact.agda': [
        'bandLower', 'bandUpper', 'bandLowerPositive', 'adjacentBoundaryEquality', 'InBand',
        'adjacentBandsDisjoint', 'sameValueCannotOccupyAdjacentBands', 'advanceExponent',
        'scaleBelowSuccessor', 'bandUpperSuccStrict', 'bandUpperAdvanceStrict',
        'bandsOrderedByPositiveGap', 'positiveGapBandsDisjoint',
    ],
    'DASHI/ComputerScience/TekumParsedExactTriadicWeldExact.agda': ['exactPow3MatchesBalancedPow3', 'parsedExactBaseUnit', 'parsedExactAdjustmentInteger', 'parsedExactScale', 'parsedExactUnsignedSignificandInteger'],
    'DASHI/ComputerScience/TekumParsedExactRationalCoordinatesExact.agda': ['parsedSourceUnsignedNumerator', 'parsedExactNumeratorUsesSourceCoordinates', 'parsedExactDenominatorUsesSourceCoordinates', 'parsedOrdinaryRationalUsesExactSourceCoordinates'],
    'DASHI/ComputerScience/TekumOrdinaryFactorizationExact.agda': [
        'rawUnsignedSourceSignificand', 'rawSourceSignificand', 'rawSourceScale', 'rawSourceFactorization',
        'parsedOrdinaryRawFactorization', 'fromRawProduct', 'fromRawSum', 'fromRawNeg',
        'applyRationalSign', 'canonicalUnsignedSignificand', 'canonicalSignedSignificand',
        'canonicalSignedSignificandIsApplySign', 'canonicalSourceScale',
        'parsedOrdinaryCanonicalFactorization', 'parsedOrdinaryCanonicalProduct',
    ],
    'DASHI/ComputerScience/TekumParsedBandMembershipExact.agda': [
        'rawSourceFraction', 'rawUnsignedSignificandOnePlusFraction',
        'canonicalUnsignedSignificandIsSourceSignificand', 'parsedMagnitude',
        'parsedMagnitudeInExponentBand', 'parsedOrdinaryRationalIsSignedMagnitude',
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

print('Tekum static regression: regime exponent intervals, integer successor gaps, fraction injectivity, signed band magnitude, source factorization, arbitrary band separation, wheel parity, parser recovery, source negation and p-adic naturality present.')
