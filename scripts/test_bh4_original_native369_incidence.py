"""Check literal Agda 27x54 endpoint list against the original PNP solver.

This checks source ordering and endpoint identity, NOT Agda kernel proofs.
"""
from pathlib import Path
import pytest
from reactive_pnp_369 import BONDS, POINTS

ROOT = Path(__file__).resolve().parents[1]
AGDA = ROOT / "DASHI/Biology/Molecular/BH4OriginalNative369IncidenceExact.agda"


def parse_literal_agda_endpoints(text):
    """Parse only the supported total constructor grammar; fail closed."""
    anchor = "sourceNative54Endpoints ="
    if text.count(anchor) != 1:
        raise ValueError("original Agda endpoint owner missing/ambiguous")
    s = text.split(anchor, 1)[1]
    offset = 0

    def skip():
        nonlocal offset
        while offset < len(s) and s[offset].isspace():
            offset += 1

    def expect(token):
        nonlocal offset
        skip()
        if not s.startswith(token, offset):
            raise ValueError(f"unexpected source Fin/vector constructor near {offset}")
        offset += len(token)

    def fin():
        nonlocal offset
        skip()
        if s.startswith("F.zero", offset):
            offset += len("F.zero")
            return 0
        expect("(F.suc")
        result = fin() + 1
        expect(")")
        return result

    def pair():
        expect("(")
        a = fin()
        expect(",")
        b = fin()
        expect(")")
        return a, b

    def vec():
        nonlocal offset
        skip()
        if s.startswith("V.[]", offset):
            offset += len("V.[]")
            return []
        expect("(V._∷_")
        first = pair()
        rest = vec()
        expect(")")
        return [first, *rest]

    result = vec()
    if len(result) != 54:
        raise ValueError("original geometry must have exactly 54 native endpoints")
    if any(a == b or not 0 <= a < 27 or not 0 <= b < 27 for a, b in result):
        raise ValueError("original Agda endpoints are not distinct Fin 27")
    return tuple(result)


def test_agda_native_incidence_endpoints_identical_to_actual_pnp_geometry():
    literal = parse_literal_agda_endpoints(AGDA.read_text(encoding="utf-8"))
    assert len(POINTS) == 27
    assert len(BONDS) == 54
    assert len(set(BONDS)) == 54
    assert literal == BONDS
    assert all(sum(abs(a - b) for a, b in zip(POINTS[start], POINTS[end])) == 1
               for start, end in literal)


def test_agda_endpoint_parser_rejects_missing_duplicate_and_changed_bond():
    actual = AGDA.read_text(encoding="utf-8")
    with pytest.raises(ValueError):
        parse_literal_agda_endpoints(actual.replace(
            "sourceNative54Endpoints =", "oldNative54Endpoints =", 1))
    with pytest.raises(ValueError):
        parse_literal_agda_endpoints(actual + "\nsourceNative54Endpoints = V.[]")
    parsed = parse_literal_agda_endpoints(actual)
    bad = list(parsed)
    bad[0] = (bad[0][1], bad[0][0])
    assert tuple(bad) != BONDS
