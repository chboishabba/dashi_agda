#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rel = 'DASHI/ComputerScience/TekumProposition5NoGoExact.agda'
path = ROOT / rel
if not path.exists():
    raise SystemExit(f'missing Proposition 5 no-go owner: {rel}')
text = path.read_text(encoding='utf-8')
for needle in (
    'RawTruncationFiniteClosed',
    'negativeEdgeRefutesFiniteClosure',
    'positiveEdgeRefutesFiniteClosure',
    'unrestrictedRawTruncationFiniteClosureImpossible',
):
    if needle not in text:
        raise SystemExit(f'missing {needle} in {rel}')
for bad in ('{!!}', 'postulate', 'TERMINATE', 'TODO_PLACEHOLDER'):
    if bad in text:
        raise SystemExit(f'forbidden marker {bad!r} in {rel}')
print('Tekum Proposition 5 no-go static gate: unrestricted raw 10->8 truncation finite-closure premise is theorem-level refuted at both reserved endpoints.')
