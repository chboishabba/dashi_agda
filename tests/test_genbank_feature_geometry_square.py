"""Generic exact GenBank geometry / reverse-complement commuting-square tests.

Toy DNA fixture only; no biological engineering or actionability.
"""
from __future__ import annotations

import pytest

from scripts.check_genbank_feature_geometry_square import (
    mirror_geometry, verify_feature_square,
)
from test_genbank_readonly_ingest import synthetic_genbank


def interval(start: int, end: int, strand: int | None = 1) -> dict:
    return {"kind": "span", "start0": start, "end0": end,
            "start1": start + 1, "end1": end, "strand": strand}


def test_actual_biopython_reverse_complement_and_compound_square():
    result = verify_feature_square(synthetic_genbank(), "fixture:toy")
    assert result["source_sequence_length"] == 80
    assert result["topology"] == "circular"
    assert result["original_feature_count"] == 2
    assert result["reverse_complement_feature_count"] == 2
    assert result["all_source_feature_geometry_commutes"]
    assert result["double_reverse_complement_sequence_equal"]
    assert result["double_reverse_complement_geometry_equal"]
    assert result["topology_preserved"]
    assert result["all_checks_passed"]
    assert not result["kernel_accepted_formal_parser_theorem"]
    assert not result["source_bytes_emitted"]


def test_exact_reverse_strand_and_one_based_coordinates():
    observed = mirror_geometry(interval(12, 40, -1), 80)
    assert observed == interval(40, 68, 1)
    assert mirror_geometry(observed, 80) == interval(12, 40, -1)
    assert mirror_geometry(interval(12, 40, None), 80)["strand"] is None


def test_join_order_reverses_and_origin_crossing_is_preserved():
    joined = {
        "kind": "compound", "operator": "join", "strand": 1,
        "parts": [interval(71, 80), interval(0, 8)],
    }
    observed = mirror_geometry(joined, 80)
    assert observed["kind"] == "compound"
    assert observed["operator"] == "join"
    assert observed["strand"] == -1
    # In a stranded join, Biopython preserves biological part order.
    assert observed["parts"] == [interval(0, 9, -1),
                                 interval(72, 80, -1)]
    assert mirror_geometry(observed, 80) == joined


def test_order_qualifier_remains_distinct_from_join():
    ordered = {"kind": "compound", "operator": "order", "strand": -1,
               "parts": [interval(11, 20, -1), interval(30, 40, -1)]}
    mirrored = mirror_geometry(ordered, 80)
    assert mirrored["operator"] == "order"
    assert mirror_geometry(mirrored, 80) == ordered


@pytest.mark.parametrize("bad", [
    interval(12, 90), interval(0, 0),
    {"kind": "span", "start0": 0, "end0": 5,
     "start1": 0, "end1": 5, "strand": 1},
    {"kind": "compound", "operator": "join", "strand": 1,
     "parts": [interval(0, 1)]},
    {"kind": "compound", "operator": "weld", "strand": 1,
     "parts": [interval(0, 1), interval(2, 3)]},
])
def test_invalid_geometry_rejected(bad):
    with pytest.raises(ValueError):
        mirror_geometry(bad, 80)


def test_all_none_parts_reverse_source_part_order():
    joined = {
        "kind": "compound", "operator": "join", "strand": None,
        "parts": [interval(71, 80, None), interval(0, 8, None)],
    }
    result = mirror_geometry(joined, 80)
    assert result["parts"] == [
        interval(72, 80, None), interval(0, 9, None),
    ]
    assert mirror_geometry(result, 80) == joined


def test_mixed_part_strands_do_not_reverse_order():
    # Compound .strand is None for a mixture, but Biopython does NOT
    # reverse the ordered parts unless every child strand is None.
    joined = {
        "kind": "compound", "operator": "join", "strand": None,
        "parts": [interval(2, 4, 1), interval(7, 9, -1)],
    }
    result = mirror_geometry(joined, 20)
    assert result["parts"] == [
        interval(16, 18, -1), interval(11, 13, 1),
    ]
    assert mirror_geometry(result, 20) == joined
