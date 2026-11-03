"""Generic synthetic tests. No molecular designs or operable gene sequences."""
from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.genbank_component_registry import (  # noqa: E402
    AUTHORITY, candidate_review_graph, project_component_registry,
)


def span(a: int, b: int, strand: int = 1) -> dict:
    return {"kind": "span", "start0": a, "end0": b,
            "start1": a + 1, "end1": b, "strand": strand}


def feat(index: int, key: str, q: dict | None = None, loc: dict | None = None) -> dict:
    return {
        "index": index, "type": key,
        "location": loc or span(index * 10, index * 10 + 5),
        "qualifiers": [{"key": k, "values": [v] if isinstance(v, str) else v}
                       for k, v in (q or {}).items()],
        "location_as_parsed": str(index * 10 + 1) + ".." + str(index * 10 + 5),
    }


def report(features: list[dict], topo: str = "circular") -> dict:
    return {
        "schema": "dashi.genbank.readonly.v1",
        "source": {"source_ref": "fixture:toy", "creator": "fixture creator",
                   "source_revision": "fixture-revision",
                   "raw_byte_count": 1500,
                   "raw_sha256": hashlib.sha256(b"toy").hexdigest()},
        "molecule": {"sequence_length": 5000,
                     "molecule_type": "DNA", "topology": topo,
                     "sequence_sha256": hashlib.sha256(b"only a stub hash").hexdigest()},
        "feature_count": len(features), "features": features,
        "authority_boundary": dict(AUTHORITY),
        "biological_function_verified": False,
        "protein_identity_verified": False,
    }


def test_categories_are_distinct_and_source_preserved():
    doc = report([
        feat(0, "source"),
        feat(1, "gene", {"gene": "illustrative"}),
        feat(2, "CDS", {"label": "coding annotation"}),
        feat(3, "promoter", {"label": "regulation"}),
        feat(4, "rep_origin"),
        feat(5, "repeat_region", {"label": "transposon-like display label"}),
        feat(6, "misc_feature", {"label": "unknown"}),
    ])
    reg = project_component_registry(doc)
    classes = [x["source_feature_class"] for x in reg["components"]]
    assert classes == [
        "source_metadata", "gene_annotation", "coding_sequence_annotation",
        "regulatory_annotation", "replication_annotation", "repeat_annotation",
        "unclassified_annotation",
    ]
    assert reg["feature_count"] == 7
    assert reg["record"]["replicon_context"] == "unresolved"
    assert not reg["record"]["circular_implies_plasmid"]
    assert reg["components"][5]["mobile_element_type_as_annotated"] is None
    assert reg["components"][5]["source_short_labels"] == ["transposon-like display label"]
    assert reg["authority_boundary"] == AUTHORITY
    assert not reg["gene_or_protein_function_verified"]


def test_mobile_element_subtype_requires_feature_key_and_qualifier():
    doc = report([
        feat(0, "mobile_element", {"mobile_element_type": "transposon"}),
        feat(1, "mobile_element", {"mobile_element_type": "retrotransposon:sample"}),
        feat(2, "repeat_region", {"label": "transposon"}),
        feat(3, "mobile_element"),
        feat(4, "mobile_element", {"mobile_element_type": "other"}),
        feat(5, "misc_feature", {"mobile_element_type": "transposon"}),
    ])
    reg = project_component_registry(doc)
    assert reg["components"][0]["mobile_element_type_as_annotated"]["source_type"] == "transposon"
    assert reg["components"][1]["mobile_element_type_as_annotated"]["source_name"] == "sample"
    assert reg["components"][2]["mobile_element_type_as_annotated"] is None
    assert reg["components"][3]["mobile_element_type_as_annotated"] is None
    assert reg["components"][4]["mobile_element_type_as_annotated"] is None
    assert reg["components"][5]["source_feature_class"] == "unclassified_annotation"
    origins = [h["diagnostic_origin"] for h in reg["review_holds"]]
    assert "missing_or_ambiguous_mobile_element_type" in origins
    assert "unrecognized_mobile_element_type" in origins
    assert "mobile_type_on_non_mobile_feature" in origins
    assert all(not x["functional_activity_verified"] and
               not x["physical_insert_or_mobility_verified"]
               for x in reg["components"])


def test_explicit_plasmid_vs_chromosome_do_not_follow_topology():
    p = project_component_registry(report([feat(0, "source", {"plasmid": "toy-plasmid"})], "linear"))
    assert p["record"]["replicon_context"] == "source-annotated-plasmid"
    assert p["record"]["topology"] == "linear"
    c = project_component_registry(report([feat(0, "source", {"chromosome": "1"})], "circular"))
    assert c["record"]["replicon_context"] == "source-annotated-chromosome"
    assert c["record"]["topology"] == "circular"
    assert not c["record"]["chromosomal_integration_inferred"]


def test_source_conflict_preserved_as_hold_not_picked_silently():
    reg = project_component_registry(report([
        feat(0, "source", {"plasmid": "P", "chromosome": "chr1"}),
    ]))
    assert reg["record"]["replicon_context"] == "source-qualifier-conflict"
    assert "source_replicon_context_conflict" in [h["diagnostic_origin"]
                                                for h in reg["review_holds"]]


def test_regulatory_subtype_source_key_not_inferred_from_label():
    reg = project_component_registry(report([
        feat(0, "regulatory", {"regulatory_class": "enhancer"}),
        feat(1, "regulatory", {"label": "promoter"}),
        feat(2, "misc_feature", {"label": "promoter"}),
    ]))
    assert reg["components"][0]["source_feature_class"] == "regulatory_annotation"
    assert reg["components"][2]["source_feature_class"] == "unclassified_annotation"
    assert "missing_or_ambiguous_regulatory_class" in [h["diagnostic_origin"]
                                                      for h in reg["review_holds"]]


def test_compound_and_reverse_feature_geometry_preserved():
    loc = {"kind": "compound", "operator": "join", "strand": -1,
           "parts": [span(4500, 5000, -1), span(0, 200, -1)]}
    reg = project_component_registry(report([feat(0, "repeat_region", loc=loc)]))
    assert reg["components"][0]["source_location"] == loc
    assert reg["components"][0]["source_location"]["parts"][0]["strand"] == -1


@pytest.mark.parametrize("broken", [
    {"start1": 0}, {"end1": 100}, {"start0": -1}, {"end0": 6000},
    {"strand": 14}, {"start0": True},
])
def test_invalid_source_geometry_fails_closed(broken):
    f = feat(0, "gene")
    f["location"].update(broken)
    with pytest.raises(ValueError):
        project_component_registry(report([f]))


def test_report_claims_cannot_be_promoted():
    doc = report([feat(0, "source")])
    doc["authority_boundary"]["promotion_authority"] = True
    with pytest.raises(ValueError, match="authority"):
        project_component_registry(doc)
    doc = report([feat(0, "source")])
    doc["protein_identity_verified"] = True
    with pytest.raises(ValueError, match="authority"):
        project_component_registry(doc)


def test_external_crossref_is_a_candidate_not_same_as():
    reg = project_component_registry(report([
        feat(0, "gene", {"gene": "toy", "db_xref": "SO:0000704"}),
    ]))
    c = reg["components"][0]
    assert c["source_db_xref_candidates"] == ["SO:0000704"]
    assert c["externally_curated_identity_verified"] is False
    assert "source_label_or_crossref_identity_unverified" in [
        h["diagnostic_origin"] for h in reg["review_holds"]]


def test_graph_projections_source_reopenable_and_without_api_claim():
    reg = project_component_registry(report([feat(0, "gene"), feat(1, "mobile_element",
                            {"mobile_element_type": "insertion sequence"})]))
    g = candidate_review_graph(reg)
    assert len(g["candidate_statements"]) == 2
    assert all(x["status"] == "candidate" and x["provenance_refs"]
               for x in g["candidate_statements"])
    assert not g["native_ITIR_or_SLR_API_conformance"]
    assert not g["external_Wikidata_edits"]


def test_cli_from_parser_report_is_reproducible(tmp_path):
    path, out = tmp_path / "report.json", tmp_path / "registry.json"
    path.write_text(json.dumps(report([feat(0, "gene")])) + "\n")
    subprocess.run([sys.executable, "-m", "scripts.genbank_component_registry",
                    "--report", str(path), "--output", str(out)],
                   check=True, cwd=Path(__file__).resolve().parents[1])
    obj = json.loads(out.read_text())
    assert obj["component_classes"] == {"gene_annotation": 1}
    assert obj["record"]["replicon_context"] == "unresolved"
