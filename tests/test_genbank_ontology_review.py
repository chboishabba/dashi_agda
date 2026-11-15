"""Source-reopenable GenBank ontology holds; no automatic cross-ID weld."""
import copy

import pytest

from scripts.genbank_readonly_ingest import parse_genbank_bytes
from scripts.genbank_ontology_review import project_review_worklist

from test_genbank_readonly_ingest import synthetic_genbank


def test_source_label_creates_review_hold_not_identity():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    work = project_review_worklist(doc)
    assert work["hold_count"] == 2
    assert all(row["kind"] == "external_identity_review"
               for row in work["review_holds"])
    assert not work["external_identity_auto_weld"]
    assert not work["wikidata_public_edit_permission"]
    assert not work["native_ITIR_MCP_or_SLR_S29_conformance_claim"]
    assert all(row["source_reopen_refs"] for row in work["review_holds"])
    assert all(not row["establishes_claim_truth"]
               for row in work["review_holds"])


def test_missing_CDS_qualifiers_produce_distinct_review_gaps():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    doc["features"][0]["type"] = "CDS"
    work = project_review_worklist(doc)
    kinds = [row["kind"] for row in work["review_holds"]]
    assert "cds_gene_unresolved" in kinds
    assert "cds_product_unresolved" in kinds
    assert "cds_translation_unresolved" in kinds
    assert "cds_codon_start_unresolved" in kinds
    assert work["hold_count"] == 6
    assert all(row["proposed_action"] == "hold-for-review"
               for row in work["review_holds"])


def test_ontology_review_rejects_promoted_source():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    doc["authority_boundary"]["read_only"] = False
    with pytest.raises(ValueError, match="promoted"):
        project_review_worklist(doc)


def test_review_identity_deterministic_under_replay():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    a, b = project_review_worklist(doc), project_review_worklist(copy.deepcopy(doc))
    assert a == b
