"""Original creator source-only geometry receipt and no-promotion checks."""
import json
from pathlib import Path

DATA = (
    Path(__file__).resolve().parents[1]
    / "docs/biology/data/ThoughtEmporiumThreeSourceGeometryIndependentAudit.json"
)


def test_all_original_creator_features_have_source_geometry_receipts():
    receipt = json.loads(DATA.read_text(encoding="utf-8"))
    assert receipt["schema"] == "dashi.genbank.source-geometry-independent-audit.v2"
    assert receipt["source_feature_count_total"] == 95
    assert receipt["all_features_valid"] is True
    records = receipt["records"]
    assert len(records) == 3
    assert [r["features"] for r in records] == [22, 53, 20]
    assert [r["joined_features"] for r in records] == [1, 0, 0]
    assert sum(r["reverse_strand_spans"] for r in records) == 25
    assert all(r["coordinate_bounds_and_mirror_twice_pass"] for r in records)
    assert all(not r["failed_feature_indices"] for r in records)
    assert all("all child part strands are None" in r["rule"]
               for r in records)


def test_synthetic_reference_and_kernel_authority_stay_separate():
    receipt = json.loads(DATA.read_text(encoding="utf-8"))
    reference = receipt["independent_synthetic_biopython_reference"]
    assert reference["biopython_version"] == "1.86"
    assert reference["case_count"] == 2000
    assert reference["failures"] == 0
    assert reference["mixed_part_strand_cases"] == 1471
    assert reference["uniform_part_strand_cases"] == 529
    assert receipt["exact_head_python_checkout_run"] is False
    assert receipt["agda_kernel_accepted"] is False
    assert receipt["native_ontology_proved"] is False
    assert receipt["original_bytes_emitted"] is False
