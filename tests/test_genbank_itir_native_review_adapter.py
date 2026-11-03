"""Native ITIR review-packet input contract over GenBank source annotations.

This does not simulate a native ITIR acceptance receipt. The optional test
that imports ITIR's actual package runs only when it is installed.
"""
from __future__ import annotations

import copy

import pytest

from scripts.genbank_component_registry import project_component_registry
from scripts.genbank_itir_native_review_adapter import (
    NATIVE_VERSION, SCHEMA, build_native_review_input, invoke_native_itir,
)
from test_genbank_component_registry import feat, report


def toy_registry():
    return project_component_registry(report([
        feat(0, "source"),
        feat(1, "promoter", {"label": "example-promoter"}),
        feat(2, "mobile_element", {"mobile_element_type": "insertion sequence"}),
    ]))


def test_itir_input_matches_real_domain_tools_required_shape():
    packet = build_native_review_input(toy_registry())
    assert packet["schema"] == SCHEMA
    assert packet["expected_native_version"] == NATIVE_VERSION
    assert packet["native_target_tool"] == (
        "itir_mcp.domain_tools.wikidata_review_packet"
    )
    assert not packet["native_tool_executed"]
    data = packet["input"]
    assert len(data["statements"]) == 3
    assert len(data["constraints"]) >= 1
    assert all(row["statement_id"] and row["fact"]
               and row["provenance_refs"] and row["status"] == "candidate"
               for row in data["statements"])
    assert all(row["constraint_id"] and row["message"]
               and row["candidate_refs"] and row["provenance_refs"]
               for row in data["constraints"])
    assert data["tooling_profile"]["tool_id"]
    assert data["tooling_profile"]["read_only"]
    assert data["tooling_profile"]["candidate_only"]
    assert not data["tooling_profile"]["authority_boundary"]["promotion_authority"]
    assert packet["no_external_QID_synthesised"]
    assert not packet["source_bases_emitted"]


def test_cannot_forward_elevated_source_or_protein_claim():
    source = toy_registry()
    source["authority_boundary"]["promotion_authority"] = True
    with pytest.raises(ValueError, match="authority"):
        build_native_review_input(source)
    source = toy_registry()
    source["gene_or_protein_function_verified"] = True
    with pytest.raises(ValueError, match="function"):
        build_native_review_input(source)


def test_candidates_are_deterministic_and_do_not_make_qid_claims():
    a = build_native_review_input(toy_registry())
    b = build_native_review_input(copy.deepcopy(toy_registry()))
    assert a == b
    assert all("wikidata:Q" not in s["statement_id"]
               for s in a["input"]["statements"])


def test_native_ITIR_function_only_when_installed():
    native = pytest.importorskip("itir_mcp.domain_tools")
    assert hasattr(native, "wikidata_review_packet")
    source = build_native_review_input(toy_registry())
    receipt = invoke_native_itir(source)
    assert receipt["native_tool_executed"] is True
    assert receipt["native_version"] == NATIVE_VERSION
    assert receipt["statement_count"] == 3
    assert receipt["constraint_count"] >= 1
    assert receipt["candidate_only"] is True
    assert receipt["external_wikidata_edited"] is False
    assert receipt["persistent_ITIR_or_SLR_store_changed"] is False
