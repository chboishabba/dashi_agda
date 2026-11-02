#!/usr/bin/env python3
"""RED-first structural and attribution firewalls for the BH4 ontology exporter."""
from __future__ import annotations

from copy import deepcopy
from build_bh4_pathway_ontology import build, jsonld


def fixture():
    matrix = {
        "schema": "dashi.bh4-stoichiometric-matrix.v1",
        "reaction_index": ["RHEA:19897"],
        "species_index": ["CHEBI:123", "CHEBI:456"],
        "species_count": 2, "reaction_count": 1,
        "matrix": [[-1], [1]],
        "columns": [{"rhea_id": "RHEA:19897", "nonzero_entries": [
            {"species": "CHEBI:123", "signed_coefficient": -1},
            {"species": "CHEBI:456", "signed_coefficient": 1}]}],
        "external_exchange": [], "finite_formula_residuals": [{"rhea_id": "RHEA:777", "reason": "R-group"}]
    }
    rhea = {"schema": "dashi.rhea-chebi-bh4-panel.v2",
            "rhea_release_reference": "2026_03", "source_uniprot_panel": "sha256:test",
            "reactions": [{"rhea_id": "RHEA:19897", "formula_charge_ready": True,
                           "participant_sparql_response_sha256": "sha256:rxn",
                           "raw_sha256": "sha256:rhea-rest",
                           "row": {"Gene Ontology": "GO:0001234",
                                   "Cross-reference (Reactome)": "R-HSA-12345.1",
                                   "Cross-reference (KEGG)": "R01716",
                                   "Cross-reference (MetaCyc)": "PABASYN-RXN"},
                           "participants": [
                               {"chebi_id": "CHEBI:123", "side": "substrate", "coefficient": 1},
                               {"chebi_id": "CHEBI:456", "side": "product", "coefficient": 1}
                           ]}]}
    xp = {"schema": "dashi.bh4-xpollenation.v1",
          "neighbourhoods": [{
              "subject": {"namespace": "rhea", "identifier": "RHEA:19897"},
              "authority": "navigation-enrichment-only", "establishesProof": False,
              "establishesPayment": False,
              "edges": [
                  {"edgeId": "a", "subject": {"namespace": "rhea", "identifier": "RHEA:19897"},
                   "relation": "reaction-participant",
                   "object": {"namespace": "chebi", "identifier": "CHEBI:123"},
                   "sourceRef": "Rhea", "sourceRevision": "2026_03",
                   "acquisitionReceipt": "sha256:rxn", "promotionAllowed": False},
                  {"edgeId": "b", "subject": {"namespace": "rhea", "identifier": "RHEA:19897"},
                   "relation": "catalysed-by",
                   "object": {"namespace": "uniprot", "identifier": "P35228"},
                   "sourceRef": "UniProt", "sourceRevision": "2026_03",
                   "acquisitionReceipt": "sha256:panel", "promotionAllowed": False}
              ]}]}
    claims = {"schema": "dashi.kitzerow-bh4-claim-ledger.v1", "claims": [{
        "source_id": "SRC-KIT-2024-08",
        "source_locator": "DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact",
        "repo_reconstruction_owner": "DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact",
        "subject": "BH4 pool", "predicate": "candidate influence", "object": "NOS state",
        "status": "source-reconstruction-candidate",
        "independent_primary_text_verification": False}]}
    return matrix, rhea, xp, claims


def rejects(matrix, rhea, xp, claims) -> None:
    try:
        build(matrix, rhea, xp, claims)
    except ValueError:
        return
    raise AssertionError("invalid ontology/claim promotion unexpectedly admitted")


def main() -> int:
    m, r, x, c = fixture()
    result = build(m, r, x, c)
    assert result["schema"] == "dashi.bh4-pathway-ontology-interop.v1"
    assert len(result["reactions"]) == 1 and len(result["species"]) == 2
    assert len(result["author_hypothesis_edges"]) == 1
    assert len(result["external_edges"]) == 2
    assert len(result["excluded_nonfinite_reactions"]) == 1
    assert result["reactions"][0]["rate_law"] is None
    assert result["species"][0]["compartment"] is None
    assert result["promotion_boundary"]["ontology_match_pays_flux"] is False
    ld = jsonld(result)
    assert len(result["ontology_cross_references"]) == 2
    assert len(result["unparsed_external_annotation_fields"]) == 2
    assert {x["source_field"] for x in result["unparsed_external_annotation_fields"]} == {
        "Cross-reference (KEGG)", "Cross-reference (MetaCyc)"}
    assert next(x for x in result["ontology_cross_references"] if
                x["target"]["namespace"] == "reactome")["target"]["identifier"] == "R-HSA-12345.1"
    assert {x["target"]["namespace"] for x in result["ontology_cross_references"]} == {"go", "reactome"}
    assert all(not x["same_biological_event_verified"] for x in result["ontology_cross_references"])
    assert len(ld["@graph"]) == 6
    assert all("owl:sameAs" not in str(node) for node in ld["@graph"])
    # Creator-observed reaction selection is a separate provenance owner,
    # not a synonym for the original 16-UniProt source-selected panel.
    source_chart = deepcopy(r)
    source_chart.update({
        "schema": "dashi.rhea-chebi-bh4-source-chart.v1",
        "creator": "Kimberly Kitzerow",
        "source_chart_publication": "https://www.researchgate.net/publication/377218425_BH4FolateCobalaminHomocysteine_Pathway",
        "source_chart_pdf_sha256_verified": False,
        "whole_creator_network_complete": False,
        "source_chart_index_sha256": "1" * 64,
        "source_rhea_ids_requested": ["RHEA:19897"],
        "rhea_rows_acquired": 1,
        "rhea_rows_failed": 0,
        "errors": [],
    })
    original = build(m, source_chart)
    assert original["model_kind"] == "creator-chart-selected-rhea-curated-biochemistry-subset"
    assert original["source_releases"]["creator_original_pdf_verified"] is False
    assert original["source_releases"]["creator_chart_source"].startswith("https://")
    assert original["author_hypothesis_edges"] == []
    assert original["promotion_boundary"]["source_chart_selection_is_complete_author_network"] is False
    bad_chart = deepcopy(source_chart)
    bad_chart["whole_creator_network_complete"] = True
    rejects(m, bad_chart, None, None)
    bad_chart = deepcopy(source_chart)
    bad_chart["source_rhea_ids_requested"] = ["RHEA:99999"]
    rejects(m, bad_chart, None, None)
    bad = deepcopy(m); bad["matrix"] = [[-2], [1]]
    rejects(bad, r, x, c)
    bad = deepcopy(r); del bad["reactions"][0]["raw_sha256"]
    rejects(m, bad, x, c)
    bad = deepcopy(r); bad["reactions"].append(deepcopy(bad["reactions"][0]))
    rejects(m, bad, x, c)
    bad = deepcopy(x); bad["neighbourhoods"][0]["edges"][0]["sameObjectVerified"] = True
    bad["neighbourhoods"][0]["edges"][0]["sameObjectClaimed"] = True
    rejects(m, r, bad, c)
    bad = deepcopy(x)
    bad["neighbourhoods"][0]["edges"][0]["sameObjectVerified"] = True
    bad["neighbourhoods"][0]["edges"][0]["sameObjectClaimed"] = True
    bad["neighbourhoods"][0]["edges"][0]["relation"] = "exact-same-object"
    rejects(m, r, bad, c)
    bad = deepcopy(r); bad["reactions"][0]["participants"][0]["coefficient"] = 2
    rejects(m, bad, x, c)
    # Non-ChEBI Rhea compound identifiers remain source-specific, not
    # spuriously promoted to a ChEBI accession.
    alternate = "http://rdf.rhea-db.org/compound/fixture-456"
    no_chebi_matrix = deepcopy(m)
    no_chebi_matrix["species_index"][1] = alternate
    no_chebi_matrix["columns"][0]["nonzero_entries"][1]["species"] = alternate
    no_chebi_rhea = deepcopy(r)
    no_chebi_rhea["reactions"][0]["participants"][1]["chebi_id"] = None
    no_chebi_rhea["reactions"][0]["participants"][1]["compound_uri"] = alternate
    no_chebi_result = build(no_chebi_matrix, no_chebi_rhea, x, c)
    assert no_chebi_result["species"][1]["coordinate"]["namespace"] == "rhea-source-participant"
    assert no_chebi_result["species"][1]["coordinate"]["uri"] is None
    bad = deepcopy(m); bad["external_exchange"] = [1]
    rejects(bad, r, x, c)
    bad = deepcopy(x); bad["neighbourhoods"][0]["edges"][0]["promotionAllowed"] = True
    rejects(m, r, bad, c)
    bad = deepcopy(x); bad["neighbourhoods"][0]["edges"][0]["object"]["identifier"] = "CHEBI:999"
    rejects(m, r, bad, c)
    bad = deepcopy(c); bad["claims"][0]["independent_primary_text_verification"] = True
    rejects(m, r, x, bad)
    bad = deepcopy(c); bad["claims"][0]["source_id"] = "unsourced"
    rejects(m, r, x, bad)
    print("bh4 pathway ontology interop regression: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
