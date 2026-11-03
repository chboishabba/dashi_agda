"""Non-operational GenBank source-inventory parity and negative tests."""
import copy

from scripts.check_genbank_source_inventory import (
    git_blob_sha,
    source_location_spelling,
    verify_inspected_source,
)
from scripts.genbank_readonly_ingest import parse_genbank_bytes
from tests.test_genbank_readonly_ingest import synthetic_genbank


def toy_inspection():
    raw = synthetic_genbank()
    report = parse_genbank_bytes(raw, source_ref="fixture:toy")
    features = []
    for feature in report["features"]:
        labels = [x for row in feature["qualifiers"]
                  if row["key"] == "label" for x in row["values"]]
        features.append({
            "index": feature["index"],
            "type": feature["type"],
            "raw_location": source_location_spelling(feature["location"]),
            "source_label": ('"' + labels[0] + '"') if labels else None,
            "qualifier_names": [row["key"] for row in feature["qualifiers"]],
        })
    inventory = {
        "schema": "dashi.genbank.creator-source-observation.v1",
        "source": {"git_blob_sha": git_blob_sha(raw)},
        "observed": {
            "length_declared": 80,
            "length_sequence_letters": 80,
            "topology": "circular",
            "feature_count": 2,
            "feature_types": report["feature_types"],
        },
        "features": features,
    }
    return raw, report, inventory


def test_synthetic_exact_parity():
    raw, report, inventory = toy_inspection()
    receipt = verify_inspected_source(report, inventory, raw)
    assert receipt["all_source_features_match"]
    assert receipt["original_blob_identity_matches"]
    assert receipt["sequence_or_phenotype_authority"] is False


def test_reject_wrong_git_blob():
    raw, report, inventory = toy_inspection()
    inventory["source"]["git_blob_sha"] = "f" * 40
    receipt = verify_inspected_source(report, inventory, raw)
    assert not receipt["all_source_features_match"]
    assert "original Git blob mismatch" in receipt["problems"]


def test_reject_wrong_reverse_strand_and_compound_order():
    raw, report, inventory = toy_inspection()
    inventory["features"][0]["raw_location"] = "3..11"
    receipt = verify_inspected_source(report, inventory, raw)
    assert "feature 0: location, strand or part order mismatch" in receipt["problems"]
    _, report, inventory = toy_inspection()
    inventory["features"][1]["raw_location"] = "join(1..8,72..80)"
    receipt = verify_inspected_source(report, inventory, raw)
    assert "feature 1: location, strand or part order mismatch" in receipt["problems"]


def test_reject_qualifier_drift_and_feature_count():
    raw, report, inventory = toy_inspection()
    inventory["features"][1]["qualifier_names"].reverse()
    receipt = verify_inspected_source(report, inventory, raw)
    assert "feature 1: qualifier order mismatch" in receipt["problems"]
    _, report, inventory = toy_inspection()
    inventory["observed"]["feature_count"] = 3
    receipt = verify_inspected_source(report, inventory, raw)
    assert "feature count mismatch" in receipt["problems"]
