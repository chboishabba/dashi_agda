#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/ComputerScience/TekumParsedAnchorListExact.agda': [
        'parsedAnchorList',
        'rejoinPayloadReverseList',
        'rejoinParsedAnchorReverseList',
        'successfulParseAnchorList',
    ],
    'DASHI/ComputerScience/TekumParsedAdjacentCarryExtractExact.agda': [
        'adjacentParsedLists',
        'sameRegimeExponentFieldEqual',
        'sameRegimeExponentSuccessorStrict',
        'regimeSuccessorFromParsedEquality',
        'extractPositiveAdjacentOrder',
    ],
    'DASHI/ComputerScience/TekumMonotonicityExact.agda': [
        'hunholdProposition4PositiveParsedAdjacent',
    ],
}

for rel, needles in required.items():
    path = ROOT / rel
    if not path.exists():
        raise SystemExit(f'missing Prop. 4 extractor owner: {rel}')
    text = path.read_text(encoding='utf-8')
    for needle in needles:
        if needle not in text:
            raise SystemExit(f'missing {needle} in {rel}')
    for bad in ('{!!}', 'postulate', 'TERMINATE', 'TODO_PLACEHOLDER'):
        if bad in text:
            raise SystemExit(f'forbidden marker {bad!r} in {rel}')

print('Tekum Prop. 4 extractor static gate: parser LST list normal form, adjacent carry extraction, and parsed-adjacent monotonicity endpoint are present.')
