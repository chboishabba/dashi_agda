"""Source-backed, sequence-free taxonomy baseline for three creator files.

This tests the previously inspected original GitHub feature/qualifier names.
It is not an exact-byte execution of the new classifier on those originals.
"""
import json
from pathlib import Path

FIXTURE = (
    Path(__file__).resolve().parents[1] /
    "docs/biology/data/ThoughtEmporiumComponentTaxonomyReadOnly.json"
)


def source_rows() -> list[dict]:
    data = json.loads(FIXTURE.read_text(encoding="utf-8"))
    assert data["schema"] == "dashi.genbank.component-source-inspection.v1"
    assert data["authority_boundary"]["promotion_authority"] is False
    assert data["dna_bases_redistributed"] is False
    return data["records"]


def test_original_files_have_all_features_and_distinct_source_types():
    r = source_rows()
    assert len(r) == 3
    assert [x["feature_count"] for x in r] == [22, 53, 20]
    assert [x["original_record_length"] for x in r] == [11214, 27921, 6981]
    assert [x["github_blob_sha"] for x in r] == [
        "0578ad167666789fbfd3faa849a455c25097b90c",
        "d350cf735f0a2061d0eb9ca006ed155c20f4034f",
        "f0b0076aa86722004322f20185b9227459c8e90b",
    ]
    assert r[0]["source_feature_types"]["repeat_region"] == 3
    assert r[1]["source_feature_types"]["misc_feature"] == 23
    assert r[1]["source_feature_types"]["CDS"] == 7
    assert r[2]["source_feature_types"]["CDS"] == 7


def test_no_mobile_or_plasmid_inferred_from_circular_source():
    for row in source_rows():
        assert row["topology_declared_from_locus"] == "circular"
        assert row["explicit_mobile_element_annotation_count"] == 0
        assert row["source_qualifier_plasmid_count"] == 0
        assert row["source_qualifier_chromosome_count"] == 0
        assert row["replicon_context_from_source_qualifiers"] == "unresolved"
        assert row["assumes_plasmid_from_circular"] is False
        assert row["assumes_gene_from_label"] is False
