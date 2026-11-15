"""Generic semantic GenBank roundtrip: all annotated source fields stay intact."""
from scripts.check_genbank_semantic_roundtrip import check_semantic_roundtrip

from test_genbank_readonly_ingest import synthetic_genbank


def test_full_record_synthetic_semantics_survive_normalization():
    raw = synthetic_genbank()
    receipt = check_semantic_roundtrip(raw, source_ref="fixture:toy")
    assert receipt["all_semantic_fields_preserved"]
    assert len(receipt["checks"]) == 7
    assert all(receipt["checks"].values())
    assert receipt["source_byte_count"] > 0
    assert receipt["formal_Agda_or_Lean_kernel_certificate"] is False
    assert receipt["biological_function_verified"] is False
    assert receipt["source_bytes_copied_to_receipt"] is False
