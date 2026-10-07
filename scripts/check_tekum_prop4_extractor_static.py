#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/ComputerScience/TekumParsedAnchorListExact.agda': [
        'parsedAnchorList', 'successfulParseAnchorList',
    ],
    'DASHI/ComputerScience/TekumParsedAdjacentCarryExtractExact.agda': [
        'extractPositiveAdjacentOrder',
    ],
    'DASHI/ComputerScience/TekumProposition4PositiveChainExact.agda': [
        'ParsedAnchorChain', 'parsedAnchorChainStrict',
    ],
    'DASHI/ComputerScience/TekumFractionOrderExact.agda': [
        'canonicalFractionIntegerStrict', 'significandIntegerStrict',
    ],
    'DASHI/ComputerScience/TekumParsedAnchorCodeExact.agda': [
        'parsedAnchorCodeFormula', 'payloadCodeBound',
        'successfulParseNatCode', 'regimeCodeIsSixPlusIndex',
    ],
    'DASHI/ComputerScience/TekumParsedAnchorBlockOrderExact.agda': [
        'ParsedBlockOrder', 'parsedAnchorCodeStrictImpliesBlockOrder',
    ],
    'DASHI/ComputerScience/TekumParsedPayloadOrderExact.agda': [
        'SameRegimePayloadOrder', 'payloadCodeStrictImpliesSameRegimeOrder',
        'sameRegimePayloadOrderStrict',
    ],
    'DASHI/ComputerScience/TekumParsedAnchorStrictOrderExact.agda': [
        'parsedAnchorCodeStrictMagnitudeStrict',
    ],
    'DASHI/ComputerScience/TekumProposition4PositiveGlobalExact.agda': [
        'positiveSourceOrderRaisesAnchorCode', 'hunholdProposition4PositiveGlobal',
    ],
    'DASHI/ComputerScience/TekumProposition4NegativeGlobalExact.agda': [
        'negativeSourceOrderReversesAnchorCode', 'hunholdProposition4NegativeGlobal',
    ],
    'DASHI/ComputerScience/TekumSpecialIntegerOrderExact.agda': [
        'classifyNaRWord', 'classifyZeroWord', 'classifyInfinityWord',
        'classifiedNaRInteger', 'classifiedZeroInteger', 'classifiedInfinityInteger',
    ],
    'DASHI/ComputerScience/TekumOrderedSourceValueExact.agda': [
        'OrderedTekumValue', 'SourceOrderedDecode',
        'ordinaryIntegerStrict', 'sourceIntegerStrictImpliesOrderedStrict',
    ],
    'DASHI/ComputerScience/TekumRawAnchorRegimeBandExact.agda': [
        'rawAnchorCodeFormula', 'anchorBandParsesRegime',
    ],
    'DASHI/ComputerScience/TekumSourceAnchorRegimeBandExact.agda': [
        'fourCenterMagnitudePlusOne', 'nonSpecialAnchorBand',
    ],
    'DASHI/ComputerScience/TekumSourceParserTotalityExact.agda': [
        'nonSpecialParseTotal', 'totalSourceParse',
    ],
    'DASHI/ComputerScience/TekumProposition4GlobalExact.agda': [
        'sourceOrderedValue', 'hunholdProposition4Global',
    ],
    'DASHI/ComputerScience/TekumProposition4PaperExact.agda': [
        'TekumOrderedValue', 'integerCodeOrderAgreesWithTekum',
        'hunholdProposition4',
    ],
}

for rel, needles in required.items():
    path = ROOT / rel
    if not path.exists():
        raise SystemExit(f'missing Prop. 4 max-cut owner: {rel}')
    text = path.read_text(encoding='utf-8')
    for needle in needles:
        if needle not in text:
            raise SystemExit(f'missing {needle} in {rel}')
    for bad in ('{!!}', 'postulate', 'TERMINATE', 'TODO_PLACEHOLDER'):
        if bad in text:
            raise SystemExit(f'forbidden marker {bad!r} in {rel}')

print('Tekum Prop. 4 max-cut static gate: arbitrary radix-block order, positive/negative ordinary order, exact special endpoints, core-width parser totality, full source ordered-code endpoint, and the paper-facing Proposition 4 interface are present.')
