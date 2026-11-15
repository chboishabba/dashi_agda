"""Receipt regression: do not silently promote local prototype to kernel acceptance."""
import json
from pathlib import Path

DATA = (Path(__file__).resolve().parents[1] /
        "docs/biology/data/ThoughtEmporiumMagnetoreceptionLocalExecutionReceipt.json")


def test_actual_original_source_receipt_is_byte_and_feature_bound():
    r = json.loads(DATA.read_text(encoding="utf-8"))
    assert r["schema"] == "dashi.genbank.actual-creator-source-local-execution.v1"
    assert r["original_git_blob_sha"] == "0578ad167666789fbfd3faa849a455c25097b90c"
    assert r["raw_byte_count"] == 18278
    assert r["raw_sha256"] == "43e7f588788e36c7a3b7d4e794dde21311781a9eae9fd857fe5cac79b46f03d1"
    assert r["normalized_dna_sequence_sha256"] == "7e1449a229c1182bc787bf861a906b42313e5e0d6676770a9d8bfa0a7bbd71db"
    assert r["original_file_parsed_locally"] is True
    assert r["original_raw_git_blob_hash_matched"] is True
    assert r["all_source_features_match"] is True
    assert r["source_parity_problems"] == []
    assert r["feature_count"] == 22
    assert r["sequence_length"] == 11214
    assert r["candidate_only_graph_statements"] == 22
    assert r["source_reopenable_review_holds"] == 30
    assert r["local_full_record_semantic_roundtrip_passed"] is True
    assert r["serialized_roundtrip_raw_byte_count"] == 18377
    assert r["raw_byte_identical_serialization"] is False
    assert all(r["local_semantic_roundtrip_checks"].values())



def test_execution_receipt_does_not_claim_unexecuted_or_biological_gates():
    r = json.loads(DATA.read_text(encoding="utf-8"))
    for field in (
        "exact_head_pytest_executed", "agda_kernel_accepted",
        "lean_kernel_accepted", "full_record_semantic_roundtrip_proved",
        "native_ITIR_SLR_adapter_conformance_checked",
        "native_Wikidata_edit_performed", "original_bases_redistributed",
        "wet_lab_function_verified",
        "independent_human_magnetoreception_verified",
        "protein_identity_verified",
    ):
        assert r[field] is False, field
    assert "exact PR codebase" in r["verification_scope"]
