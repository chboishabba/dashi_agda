#!/usr/bin/env python3
"""Focused deterministic regression. Uses the existing ontology-exporter fixture."""
from __future__ import annotations

from copy import deepcopy
from build_bh4_pathway_ontology import build as build_pathway
from check_bh4_pathway_ontology import fixture
from build_bh4_pathway_review import build as build_review


def rejects(payload, **kwargs) -> None:
    try:
        build_review(payload, **kwargs)
    except ValueError:
        return
    raise AssertionError("unpaid review input incorrectly accepted")


def main() -> int:
    m, r, x, c = fixture()
    p = build_pathway(m, r, x, c)
    review = build_review(p)
    assert review["schema"] == "dashi.bh4-pathway-review-worklist.v1"
    assert review["promotion_boundary"]["read_only"] is True
    assert review["promotion_boundary"]["mutates_wikidata"] is False
    assert review["orientation"]["disclosure_route"] == [
        "Orient", "Project", "Why?", "Source", "Meaning", "Follow", "Next unresolved"]
    kinds = review["obligation_family_counts"]
    assert kinds["author-source"] == 1
    assert kinds["reaction-flux"] == 1
    assert kinds["exchange-flux"] == 2
    assert kinds["direction"] == 1
    assert kinds["ontology-mapping"] == 2
    assert kinds["context"] == 3
    assert kinds["chemistry"] == 1
    assert len(review["obligations"]) == 11
    assert len({row["id"] for row in review["obligations"]}) == 11
    assert all(row["source_reopen_refs"] and row["repair_disposition"] == "hold-for-review"
               and row["establishes_flux_payment"] is False
               and row["edited_external_ontology"] is False for row in review["obligations"])
    # Deterministic even with irrelevant JSON object ordering.
    assert review == build_review(deepcopy(p))

    good_source = {"schema": "dashi.bh4-source-reopen-packet.v1", "sources": [{
        "source_id": "SRC-KIT-2024-08", "source_revision": "source-rev-1",
        "snapshot_digest": "sha256:unverified", "content_locator": "public-source-ref", "visibility": "public"
    }]}
    with_source = build_review(p, source_receipts=good_source)
    author = next(x for x in with_source["obligations"] if x["kind"] == "author-source")
    assert "public-source-ref" in author["source_reopen_refs"]
    assert author["classification"] == "active-missing-evidence"
    assert with_source["external_source_envelopes_supplied"] == 1
    internal = deepcopy(good_source)
    internal["sources"][0]["visibility"] = "restricted"
    internal["sources"][0]["content_locator"] = "secret-private-path"
    held = build_review(p, source_receipts=internal)
    assert "secret-private-path" not in str(held)
    assert held["restricted_source_envelopes_not_exposed"] == 1
    assert held["candidate_publication_allowed"] is False
    invalid_visibility = deepcopy(good_source)
    del invalid_visibility["sources"][0]["visibility"]
    rejects(p, source_receipts=invalid_visibility)

    promoted = deepcopy(p)
    promoted["author_hypothesis_edges"][0]["independent_primary_text_verification"] = True
    rejects(promoted)
    promoted = deepcopy(p)
    promoted["ontology_cross_references"][0]["same_biological_event_verified"] = True
    rejects(promoted)
    promoted = deepcopy(p)
    promoted["reactions"][0]["flux_interval"] = [0, 1]
    rejects(promoted)
    promoted = deepcopy(p)
    promoted["promotion_boundary"]["ontology_match_pays_flux"] = True
    rejects(promoted)
    bad_source = deepcopy(good_source)
    bad_source["sources"].append(deepcopy(good_source["sources"][0]))
    rejects(p, source_receipts=bad_source)
    print("bh4 pathway review worklist regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
