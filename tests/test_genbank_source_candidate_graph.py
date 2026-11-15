"""Source fixture is an evidence review graph, not automatic ontology truth."""
import json
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "docs/biology/data"


def test_source_inspection_graph_has_all_original_features_and_holds():
    g = json.loads((DATA / "ThoughtEmporiumMagnetoreceptionCandidateReviewGraph.json").read_text())
    i = json.loads((DATA / "ThoughtEmporiumMagnetoreceptionGenBankSourceInventory.json").read_text())
    r = json.loads((DATA / "ThoughtEmporiumMagnetoreceptionLocalExecutionReceipt.json").read_text())
    assert g["source_git_blob_sha"] == i["source"]["git_blob_sha"]
    assert g["raw_sha256"] == r["raw_sha256"]
    assert g["source_annotation_statement_count"] == i["observed"]["feature_count"] == 22
    assert g["review_hold_count"] == r["source_reopenable_review_holds"] == 30
    for n, (feature, claim) in enumerate(zip(i["features"], g["source_inspected_annotations"])):
        assert feature["index"] == claim["feature_index"] == n
        assert feature["type"] == claim["feature_type"]
        assert feature["raw_location"] == claim["source_location"]
        assert claim["status"] == "candidate"
        assert claim["source_reopen_refs"]
        assert claim["biological_function_verified"] is False


def test_source_label_and_ontology_evidence_remain_distinct():
    g = json.loads((DATA / "ThoughtEmporiumMagnetoreceptionCandidateReviewGraph.json").read_text())
    assert g["source_inspected_annotations"][8]["feature_type"] == "misc_feature"
    assert g["source_inspected_annotations"][8]["source_label"] == "cacna1d human plus pigeon"
    assert len(g["source_scoped_hypothesis_links"]) == 1
    assert all(not x["protein_same_object_verified"] for x in g["source_scoped_hypothesis_links"])
    assert len(g["mechanism_context_not_from_source_features"]) == 2
    assert g["authority_boundary"]["promotion_authority"] is False
    assert not g["is_exact_native_ITIR_MCP_receipt"]
    assert not g["is_exact_native_SLR_S29_receipt"]
    assert not g["public_wikidata_mutations_allowed"]
    assert not g["human_magnetoreception_proved"]
    assert not g["original_sequence_bytes_redistributed"]
