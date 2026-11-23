#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': ['eval-involution', 'toIntegerSwapSign', 'toIntegerInvertWord'],
    'DASHI/Algebra/BalancedTernaryPositionalInjectiveExact.agda': ['evalIntegerCons', 'toIntegerInjective'],
    'DASHI/Algebra/BalancedTernaryRankReconstructionExact.agda': ['rankWord', 'unrankWord', 'unrankRankWord', 'rankUnrankWord'],
    'DASHI/Algebra/BalancedTernaryRankNegationExact.agda': ['rankInvertIsOpposite'],
    'DASHI/Algebra/BalancedTernaryCenteredReconstructionExact.agda': ['CenteredInteger', 'decodeEncodeCentered', 'encodeDecodeCentered', 'balancedTernaryCenteredBijection'],
    'DASHI/ComputerScience/TekumSourceAnchorCenterExact.agda': [
        'sourceAnchorCenterWord', 'sourceAnchorCenterInteger2', 'sourceAnchorCenterInteger4',
        'sourceCenterMagnitude', 'centerAtEvenWidth', 'sourceCenterNatCodeAtEvenWidth',
        'sourceCenterIntegerAtEvenWidth',
    ],
    'DASHI/ComputerScience/TekumFixedWidthBalancedArithmeticExact.agda': [
        'negateWordIsInvertWord', 'tekumBalancedArithmetic', 'concreteAnchor',
        'concreteAnchorNegationInvariant', 'sourceMidpointAnchorsToZeroWidth4',
    ],
    'DASHI/ComputerScience/TekumSourceWordDecodeExact.agda': [
        'integerToIntCodeRoundTrip', 'fractionIntCodeInteger', 'exponentIntCodeInteger',
        'parseTekumWord', 'specialClassificationAppliedToSourceWord',
    ],
    'DASHI/ComputerScience/TekumSourceWordRoundTripExact.agda': ['rejoinPayloadCorrect', 'rejoinParsedAnchorPayloadCorrect', 'rejoinPayloadDeterminesSourcePayload', 'sourceParserImageIsLossless'],
    'DASHI/ComputerScience/TekumParserSuccessfulRejoinExact.agda': [
        'decodeRegimeSound', 'parseAnchorMSBSuccessfulRejoin',
        'parseOrdinaryAnchorSuccessfulRejoin',
    ],
    'DASHI/ComputerScience/TekumSourceNegationExact.agda': [
        'signOfNegateWord', 'parseOrdinaryAnchorNegationInvariant',
        'hunholdProposition3Ordinary',
    ],
    'DASHI/ComputerScience/TekumFractionRationalRangeExact.agda': ['fractionStrictHalfBound', 'canonicalFractionIsSignedDivision'],
    'DASHI/ComputerScience/TekumFractionInjectiveExact.agda': ['canonicalFractionEqualityToRaw', 'fractionNumeratorEquality', 'canonicalFractionInjective'],
    'DASHI/ComputerScience/TekumIntegerSuccessorGapExact.agda': ['advancePositive', 'advanceCommuteSucc', 'advanceNegativeToZero', 'advanceNegativeGap', 'integerLessHasPositiveAdvance'],
    'DASHI/ComputerScience/TekumRegimeExponentIntervalExact.agda': ['regimeLower', 'regimeUpper', 'parsedExponentRange', 'RegimeStep', 'adjacentRegimeBoundary', 'stepRegimeIntervalsOrdered', 'regimeIntervalNonempty'],
    'DASHI/ComputerScience/TekumRegimeChainExact.agda': ['regimeIndex', 'regimeFromIndex', 'regimeIndexInjective', 'spanPredAtIndex', 'chainLower', 'chainUpper', 'chainIntervalsOrderedFromLess', 'regimeLowerMatchesChain', 'regimeUpperMatchesChain', 'RegimeComparison', 'compareRegimes', 'equalParsedExponentForcesRegime'],
    'DASHI/ComputerScience/TekumParsedExponentInjectiveExact.agda': ['equalParsedMagnitudesForceExponent', 'leftExponentStrictContradiction', 'rightExponentStrictContradiction'],
    'DASHI/ComputerScience/TekumParsedFieldRecoveryExact.agda': [
        'equalMagnitudeForceRegime', 'equalExponentSameRegimeForceExponentField',
        'equalMagnitudeSameRegimeForceSignificand', 'equalMagnitudeSameRegimeForceFraction',
        'equalExponentSameRegimeForceExponentMSB', 'equalMagnitudeSameRegimeForceFractionMSB',
    ],
    'DASHI/ComputerScience/TekumParsedPayloadInjectiveExact.agda': [
        'sameRegimeFieldsDeterminePayload', 'equalMagnitudeDeterminesRegimeAndPayload',
        'equalMagnitudeDeterminesRejoinedAnchor',
    ],
    'DASHI/ComputerScience/TekumSignedMagnitudeInjectiveExact.agda': [
        'OrdinarySign', 'negativePositiveDistinct', 'positiveNegativeDistinct',
        'signedPositiveInjective',
    ],
    'DASHI/ComputerScience/TekumSignedAbsoluteWordInjectiveExact.agda': [
        'signAbsoluteIntegerInjective', 'sameSignAbsoluteValueDeterminesSourceWord',
    ],
    'DASHI/ComputerScience/TekumPositiveAnchorInjectiveExact.agda': [
        'positiveMagnitudeBound', 'positiveModulusCentered', 'negatedSourceCenterRank',
        'positiveWrapExactEven', 'positiveConcreteAnchorRank', 'positiveAnchorInjective',
    ],
    'DASHI/ComputerScience/TekumSourceAnchorInjectiveExact.agda': [
        'negateWordInvolutive', 'negativeNegatesPositive',
        'sameSignAnchorDeterminesSourceWord', 'Width.EvenWidth',
    ],
    'DASHI/ComputerScience/TekumSourceWordInjectiveExact.agda': [
        'ordinaryEqualDeterminesSign', 'ordinaryEqualDeterminesMagnitude',
        'ordinaryRationalInjectiveOnParsedWords', 'hunholdProposition2Injective',
        'Width.EvenWidth (8 + extra)',
    ],
    'DASHI/ComputerScience/TekumSignificandRangeExact.agda': ['significandStrictBand', 'nextExponentLowerEqualsCurrentUpper'],
    'DASHI/ComputerScience/TekumTriadicScaleExact.agda': ['integerSucc', 'triadicScale', 'triadicScalePositive', 'rawTriadicScaleSucc', 'triadicScaleSucc', 'intCodeTriadicScaleCanonical'],
    'DASHI/ComputerScience/TekumExponentBandExact.agda': ['bandLower', 'bandUpper', 'bandLowerPositive', 'adjacentBoundaryEquality', 'InBand', 'adjacentBandsDisjoint', 'sameValueCannotOccupyAdjacentBands', 'advanceExponent', 'scaleBelowSuccessor', 'bandUpperSuccStrict', 'bandUpperAdvanceStrict', 'bandsOrderedByPositiveGap', 'positiveGapBandsDisjoint'],
    'DASHI/ComputerScience/TekumMonotoneMagnitudeExact.agda': [
        'exponentStrictForcesMagnitudeStrict',
        'sameExponentSignificandStrictForcesMagnitudeStrict',
    ],
    'DASHI/ComputerScience/TekumPositiveSourceSuccessorAnchorExact.agda': [
        'positiveSourceStepRaisesAnchorRank',
        'positiveSourceSuccessorAnchorsAreAdjacent',
    ],
    'DASHI/ComputerScience/TekumSourceOrderExact.agda': [
        'PositiveAdjacentOrder',
        'positiveAdjacentSourceCodeStrict',
        'hunholdProposition4PositiveAdjacent',
    ],
    'DASHI/ComputerScience/TekumParsedExactTriadicWeldExact.agda': ['exactPow3MatchesBalancedPow3', 'parsedExactBaseUnit', 'parsedExactAdjustmentInteger', 'parsedExactScale', 'parsedExactUnsignedSignificandInteger'],
    'DASHI/ComputerScience/TekumParsedExactRationalCoordinatesExact.agda': ['parsedSourceUnsignedNumerator', 'parsedExactNumeratorUsesSourceCoordinates', 'parsedExactDenominatorUsesSourceCoordinates', 'parsedOrdinaryRationalUsesExactSourceCoordinates'],
    'DASHI/ComputerScience/TekumOrdinaryFactorizationExact.agda': ['rawUnsignedSourceSignificand', 'rawSourceScale', 'rawSourceFactorization', 'parsedOrdinaryRawFactorization', 'fromRawProduct', 'fromRawSum', 'fromRawNeg', 'applyRationalSign', 'canonicalUnsignedSignificand', 'canonicalSignedSignificand', 'canonicalSignedSignificandIsApplySign', 'canonicalSourceScale', 'parsedOrdinaryCanonicalFactorization', 'parsedOrdinaryCanonicalProduct'],
    'DASHI/ComputerScience/TekumParsedBandMembershipExact.agda': ['rawSourceFraction', 'rawUnsignedSignificandOnePlusFraction', 'canonicalUnsignedSignificandIsSourceSignificand', 'parsedMagnitude', 'parsedMagnitudePositive', 'parsedMagnitudeInExponentBand', 'parsedOrdinaryRationalIsSignedMagnitude'],
    'DASHI/ComputerScience/TekumWheelStateParityExact.agda': ['EvenWidth', 'OddWidth', 'pow3Mod4TwoStep', 'pow3Mod4Even', 'pow3Mod4Odd', 'pow3Mod4OneImpliesEvenWidth', 'wheelQuarterIntegralityIffEvenWidth'],
    'DASHI/ComputerScience/TekumExactTriadicSemanticsExact.agda': ['pow3NonZero', 'exactTriadicRationalUsesSignedDivision'],
    'DASHI/ComputerScience/TekumProposition5CounterexampleExact.agda': [
        'negativeEdge10IsOrdinarySourceWord', 'negativeEdgeAnchorTruncatesToMidpoint',
        'negativeEdgeRoundHitsNaR', 'positiveEdge10IsOrdinarySourceWord',
        'positiveEdgeRoundHitsInfinity',
    ],
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

fixed = (ROOT / 'DASHI/ComputerScience/TekumFixedWidthBalancedArithmeticExact.agda').read_text(encoding='utf-8')
if 'allOnes = allPositiveWord n' in fixed:
    raise SystemExit('stale Hunhold anchor: Definition 7 must use alternating 1T...1T midpoint, not 11...1')
if 'allOnes = SourceCenter.sourceAnchorCenterWord n' not in fixed:
    raise SystemExit('missing literal Hunhold Definition 7 alternating source midpoint')

source = (ROOT / 'DASHI/ComputerScience/TekumSourceWordDecodeExact.agda').read_text(encoding='utf-8')
if 'Special.classifySpecial (Fixed.concreteAnchor word)' in source:
    raise SystemExit('stale special classifier: NaR/zero/infinity are reserved source words, not anchor words')
if 'Special.classifySpecial word' not in source:
    raise SystemExit('source special classifier not applied to source word')

assembly = (ROOT / 'DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda').read_text(encoding='utf-8')
if 'true true false false false true' not in assembly:
    raise SystemExit('assembly must record corrected Prop. 2 and source-domain Prop. 3 as source-paid, with Prop. 4/5 and numerical no-double-rounding still false')

print('Tekum static regression: Definition 7 midpoint and source special classification are corrected; Prop. 2 is source-reclosed with explicit even-width evidence; source-domain Prop. 3 remains present; Prop. 4 now requires the positive source-successor/anchor-successor and adjacent-order owners; Proposition 5 edge obstructions are recorded; no kernel-compilation claim is implied by this static gate.')
