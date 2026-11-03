"""Reusable GenBank ingestion tests with synthetic non-operational fixture.

The published original author's sequence is NOT copied into this test.
Tested locally on Biopython 1.86 (seven test functions passed).
"""
import copy
from io import StringIO

import pytest
from Bio import SeqIO
from Bio.Seq import Seq
from Bio.SeqFeature import CompoundLocation, FeatureLocation, SeqFeature
from Bio.SeqRecord import SeqRecord

from scripts.genbank_readonly_ingest import (
    parse_genbank_bytes,
    candidate_review_graph,
    location_normalize,
)


def synthetic_genbank() -> bytes:
    rec = SeqRecord(
        Seq("ACGT" * 20), id="TEST00001", name="toy",
        description="synthetic parser fixture",
    )
    rec.annotations["molecule_type"] = "DNA"
    rec.annotations["topology"] = "circular"
    rec.features = [
        SeqFeature(
            FeatureLocation(2, 11, strand=-1),
            type="misc_feature",
            qualifiers={"label": ["example"]},
        ),
        SeqFeature(
            CompoundLocation(
                [
                    FeatureLocation(71, 80, strand=1),
                    FeatureLocation(0, 8, strand=1),
                ],
                operator="join",
            ),
            type="repeat_region",
            qualifiers={"label": ["wrap test"], "note": ["toy"]},
        ),
    ]
    buffer = StringIO()
    SeqIO.write(rec, buffer, "genbank")
    return buffer.getvalue().encode()


def test_compound_circular_reverse_and_exact_coordinates():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    assert doc["molecule"]["sequence_length"] == 80
    assert doc["molecule"]["topology"] == "circular"
    assert doc["feature_types"] == {"misc_feature": 1, "repeat_region": 1}
    span = doc["features"][0]["location"]
    assert (span["start0"], span["start1"], span["end1"]) == (2, 3, 11)
    assert span["strand"] == -1
    joined = doc["features"][1]["location"]
    assert joined["operator"] == "join"
    assert len(joined["parts"]) == 2
    assert joined["parts"][0]["start0"] == 71
    assert joined["parts"][1]["start0"] == 0
    assert location_normalize(joined) == joined


def test_candidate_graph_provenance_and_nonpromotion():
    doc = parse_genbank_bytes(
        synthetic_genbank(), source_ref="fixture:toy", creator="fixture",
    )
    graph = candidate_review_graph(doc)
    assert len(graph["candidate_statements"]) == 2
    assert all(x["claim_tier"] == "source-annotation-only"
               for x in graph["candidate_statements"])
    assert graph["authority_boundary"]["promotion_authority"] is False
    assert not graph["automatic_wikidata_repair"]
    assert not doc["biological_function_verified"]
    assert not doc["protein_identity_verified"]
    assert "ACGTACG" not in str(doc)


def test_reject_off_by_one_coordinates():
    ast = parse_genbank_bytes(
        synthetic_genbank(), source_ref="fixture:toy",
    )["features"][0]["location"]
    broken = copy.deepcopy(ast)
    broken["start1"] = broken["start0"]
    with pytest.raises(ValueError, match="coordinate"):
        location_normalize(broken)


def test_reject_unknown_strand_and_unsupported_compound():
    ast = parse_genbank_bytes(
        synthetic_genbank(), source_ref="fixture:toy",
    )["features"][1]["location"]
    bad = copy.deepcopy(ast)
    bad["parts"][0]["strand"] = 17
    with pytest.raises(ValueError, match="strand"):
        location_normalize(bad)
    bad = copy.deepcopy(ast)
    bad["operator"] = "weld"
    with pytest.raises(ValueError, match="operator"):
        location_normalize(bad)


def test_bad_and_non_dna_input_fails_closed():
    with pytest.raises(ValueError):
        parse_genbank_bytes(b"not a GenBank file", source_ref="fixture")
    with pytest.raises(ValueError):
        parse_genbank_bytes(
            synthetic_genbank().replace(b"acgt", b"ncgt"),
            source_ref="fixture",
        )


def test_semantic_and_raw_hashes_stable():
    a = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    b = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    assert a["semantic_sha256"] == b["semantic_sha256"]
    assert a["source"]["raw_sha256"] == b["source"]["raw_sha256"]
    assert len(a["semantic_sha256"]) == 64


def test_graph_rejects_unapproved_promotions():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    doc["authority_boundary"]["promotion_authority"] = True
    with pytest.raises(ValueError, match="promoted"):
        candidate_review_graph(doc)
