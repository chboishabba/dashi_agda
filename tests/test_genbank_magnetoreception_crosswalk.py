"""Mocked source-contract tests, not a substitute for real Git-blob replay."""
import copy

import pytest

from scripts.genbank_readonly_ingest import AUTHORITY, parse_genbank_bytes
from scripts.genbank_magnetoreception_crosswalk import build_source_crosswalk
from test_genbank_readonly_ingest import synthetic_genbank


def fake_verified_contract():
    doc = parse_genbank_bytes(synthetic_genbank(), source_ref="fixture:toy")
    feature = copy.deepcopy(doc["features"][0])
    doc["features"] = []
    for index in range(22):
        row = copy.deepcopy(feature)
        row["index"] = index
        if index == 8:
            row["type"] = "misc_feature"
            row["qualifiers"] = [{
                "key": "label", "values": ["cacna1d human plus pigeon"],
            }]
        doc["features"].append(row)
    doc["feature_count"] = 22
    inventory = {
        "source": {
            "git_blob_sha": "fixture-sha",
            "source_commit": "fixture-commit",
            "creator": "The Thought Emporium / Justin Atkin",
        },
        "authority_boundary": dict(AUTHORITY),
    }
    parity = {
        "original_blob_identity_matches": True,
        "all_source_features_match": True,
        "problems": [],
        "source_blob_sha": "fixture-sha",
    }
    return doc, inventory, parity


def test_under_annotated_source_label_is_not_gene_cds_phenotype():
    report, inventory, parity = fake_verified_contract()
    out = build_source_crosswalk(report, inventory, parity)
    link = out["mechanism_links"][0]
    assert link["feature_type_in_original"] == "misc_feature"
    assert link["source_label"] == "cacna1d human plus pigeon"
    assert link["status"] == "candidate"
    assert not link["protein_same_object_verified"]
    assert not link["magnetoreception_phenotype_verified"]
    assert not out["ontology_or_wikidata_truth_promoted"]
    assert not out["original_sequence_emitted"]
    assert all(row["not_a_sequence_absence_proof"]
               for row in out["contextual_comparison_only"])


def test_source_mismatch_and_promoted_contract_are_rejected():
    report, inventory, parity = fake_verified_contract()
    parity["source_blob_sha"] = "unknown"
    with pytest.raises(ValueError, match="source mismatch"):
        build_source_crosswalk(report, inventory, parity)

    report, inventory, parity = fake_verified_contract()
    report["authority_boundary"]["promotion_authority"] = True
    with pytest.raises(ValueError, match="unverified"):
        build_source_crosswalk(report, inventory, parity)


def test_wrong_feature_label_or_type_is_rejected():
    report, inventory, parity = fake_verified_contract()
    report["features"][8]["type"] = "CDS"
    with pytest.raises(ValueError, match="label/type"):
        build_source_crosswalk(report, inventory, parity)
    report, inventory, parity = fake_verified_contract()
    report["features"][8]["qualifiers"][0]["values"] = ["not-the-source-label"]
    with pytest.raises(ValueError, match="label/type"):
        build_source_crosswalk(report, inventory, parity)


def test_unverified_parity_never_builds_claim():
    report, inventory, parity = fake_verified_contract()
    parity["all_source_features_match"] = False
    with pytest.raises(ValueError, match="unverified"):
        build_source_crosswalk(report, inventory, parity)
