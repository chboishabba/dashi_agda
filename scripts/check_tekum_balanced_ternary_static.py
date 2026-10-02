#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
required = {
    'DASHI/Algebra/BalancedTernaryIntegerExact.agda': ['eval-involution', 'threeTritExtremalPositiveWeight'],
    'DASHI/ComputerScience/TekumRegimeExponentExact.agda': ['decodeEncodeRegime', 'outerPositiveBiasIs244'],
    'DASHI/ComputerScience/TekumSSPFRACTRANBridgeExact.agda': ['positionedReopenExact', 'positionedCodeSeparatesTekumDigit', 'negativeUnitAtOneCompilesToThreeInversePrimes'],
    'DASHI/ComputerScience/TekumFieldRoleSSPAtlasExact.agda': ['canonicalRadixThreeAtlas', 'separatedRoleAtlas'],
    'DASHI/ComputerScience/TekumPrecisionCompositionExact.agda': ['truncateTwoTwiceEqualsFour'],
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

print('Tekum static regression: required owners and theorem names present.')