#!/usr/bin/env python3
from __future__ import annotations

from build_bh4_xpollenation import build


def fixture() -> tuple[dict, dict, dict, dict]:
    rhea = {
        "schema": "dashi.rhea-chebi-bh4-panel.v2",
        "protein_reaction_links": [
            {"symbol": "NOS2", "accession": "P35228", "rhea_id": "RHEA:19897"},
        ],
        "reactions": [
            {
                "rhea_id": "RHEA:19897",
                "participants": [
                    {"chebi_id": "CHEBI:123", "side": "substrate"},
                ],
            }
        ],
    }
    adjudication = {
        "schema": "dashi.bh4-sabio-adjudication.v2",
        "rows": [
            {
                "accession": "P35228",
                "entry_id": "SABIO:1",
                "parameter_name": "Km",
                "parameter_kind_hint": "affinity-like",
                "finite_matrix_rhea_ids": ["RHEA:19897"],
            }
        ],
    }
    sifts = {
        "schema": "dashi.bh4-pdbe-sifts.v2",
        "results": [
            {
                "accession": "P35228",
                "structures": [
                    {"pdb_id": "1ABC", "matching_segment_count": 2, "raw_sha256": "abc"}
                ],
            }
        ],
    }
    wikimedia = {
        "panel_schema": "dashi.wikimedia-biology-panel.v1",
        "members": [
            {
                "uniprot_accession": "P35228",
                "identity_status": "verified",
                "exact_p352_matches": [
                    {"protein_qid": "Q123", "exact_p352_match": True}
                ],
            }
        ],
    }
    return rhea, adjudication, sifts, wikimedia


def main() -> int:
    rhea, adjudication, sifts, wikimedia = fixture()
    result = build(
        ["RHEA:19897"],
        rhea=rhea,
        adjudication=adjudication,
        sifts=sifts,
        wikimedia=wikimedia,
    )
    assert result["schema"] == "dashi.bh4-xpollenation.v1"
    assert result["reaction_count"] == 1
    neighbourhood = result["neighbourhoods"][0]
    assert neighbourhood["subject"] == {"namespace": "rhea", "identifier": "RHEA:19897"}
    relations = {edge["relation"] for edge in neighbourhood["edges"]}
    assert {"catalysed-by", "reaction-participant", "kinetic-parameter-for", "protein-structure-of", "curated-cross-reference"} <= relations
    assert neighbourhood["authority"] == "navigation-enrichment-only"
    assert neighbourhood["establishesProof"] is False
    assert neighbourhood["establishesPayment"] is False
    assert all(edge["promotionAllowed"] is False for edge in neighbourhood["edges"])
    assert all("subject" in edge for edge in neighbourhood["edges"])
    qid_edges = [edge for edge in neighbourhood["edges"] if edge["object"]["namespace"] == "wikidata-qid"]
    assert qid_edges and all(edge["status"] == "identity-paid" for edge in qid_edges)
    assert qid_edges and all(edge["sameObjectClaimed"] and edge["sameObjectVerified"] for edge in qid_edges)
    print("bh4 xpollenation regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
