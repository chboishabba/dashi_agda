#!/usr/bin/env python3
"""Build a source-bound BH4 pathway/ontology exchange graph from existing receipts.

This is a DASHI interoperability reconstruction, not a newly observed
biological pathway. Ontology adjacency cannot pay a flux/clinical/causal gate.
Sources: Kitzerow 2024-01 DOI 10.13140/RG.2.2.23124.37761/1;
Kitzerow 2024-08 ResearchGate 383021907; Rhea (rhea-db.org);
UniProt (uniprot.org); ChEBI (ebi.ac.uk/chebi);
SBML Level 3 Core (sbml.org/specifications).
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

SCHEMA = "dashi.bh4-pathway-ontology-interop.v1"
CLAIM_SCHEMA = "dashi.kitzerow-bh4-claim-ledger.v1"
AUTHORITY = "navigation-and-hypothesis-only"
RHEA = re.compile(r"RHEA:[0-9]+$")
CHEBI = re.compile(r"CHEBI:[0-9]+$")
UNIPROT = re.compile(r"[A-Z0-9]{6,10}$")
GO_ID = re.compile(r"GO:[0-9]{7}$")
REACTOME_ID = re.compile(r"R-[A-Z]{3}-[0-9]+(?:\.[0-9]+)?$")
GO_IN_TEXT = re.compile(r"GO:[0-9]{7}")
REACTOME_IN_TEXT = re.compile(r"R-[A-Z]{3}-[0-9]+(?:\.[0-9]+)?")
SOURCE_IDS = {"SRC-KIT-2024-01", "SRC-KIT-2024-08", "SRC-KIT-2025-07"}


def read(path: Path | None) -> dict:
    return json.loads(path.read_text(encoding="utf-8")) if path else {}


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def coordinate(ns: str, identifier: str) -> dict:
    ensure(bool(ns and identifier), "blank ontology coordinate")
    if ns == "rhea":
        ensure(bool(RHEA.fullmatch(identifier)), "invalid Rhea coordinate: " + identifier)
        uri = "https://identifiers.org/rhea/" + identifier.split(":")[1]
    elif ns == "chebi":
        ensure(bool(CHEBI.fullmatch(identifier)), "invalid ChEBI coordinate: " + identifier)
        uri = "https://identifiers.org/chebi/" + identifier
    elif ns == "uniprot":
        ensure(bool(UNIPROT.fullmatch(identifier)), "invalid UniProt coordinate: " + identifier)
        uri = "https://identifiers.org/uniprot/" + identifier
    elif ns == "go":
        ensure(bool(GO_ID.fullmatch(identifier)), "invalid GO term")
        uri = "https://identifiers.org/go/" + identifier
    elif ns == "reactome":
        ensure(bool(REACTOME_ID.fullmatch(identifier)), "invalid Reactome event")
        uri = "https://identifiers.org/reactome/" + identifier
    else:
        # A source-provided external identifier is not assumed to have a
        # canonical resolver or an owl:sameAs relation.
        uri = None
    return {"namespace": ns, "identifier": identifier, "uri": uri}


def species_coordinate(identifier: str) -> dict:
    """Do not manufacture ChEBI membership for a Rhea compound URI/name."""
    if CHEBI.fullmatch(identifier):
        return coordinate("chebi", identifier)
    return coordinate("rhea-source-participant", identifier)


def checked_matrix(matrix: dict) -> tuple[list[str], list[str], dict[str, list[dict]]]:
    ensure(matrix.get("schema") == "dashi.bh4-stoichiometric-matrix.v1", "unexpected matrix schema")
    reactions = matrix.get("reaction_index", [])
    species = matrix.get("species_index", [])
    values = matrix.get("matrix", [])
    ensure(isinstance(reactions, list) and isinstance(species, list), "missing matrix index")
    ensure(len(reactions) == len(set(reactions)) and len(species) == len(set(species)), "duplicate matrix identity")
    ensure(all(RHEA.fullmatch(r) for r in reactions), "non-Rhea reaction")
    ensure(all(isinstance(s, str) and s and s != "unidentified" for s in species), "invalid source species")
    ensure(len(values) == len(species), "matrix species count mismatch")
    ensure(all(isinstance(row, list) and len(row) == len(reactions)
               and all(type(v) is int for v in row) for row in values),
           "matrix dimensions or coefficient type mismatch")
    ensure(matrix.get("species_count") == len(species) and matrix.get("reaction_count") == len(reactions),
           "matrix declared dimensions mismatch")
    expected = {
        rid: [{"species": s, "signed_coefficient": values[i][j]}
              for i, s in enumerate(species) if values[i][j]]
        for j, rid in enumerate(reactions)
    }
    columns = matrix.get("columns", [])
    ensure(isinstance(columns, list) and len(columns) == len(reactions), "missing columns")
    supplied = {c.get("rhea_id"): c.get("nonzero_entries") for c in columns}
    ensure(len(supplied) == len(reactions) and supplied == expected,
           "column certificates disagree with matrix")
    ensure(all(expected[r] for r in reactions), "unpaid zero-reaction column")
    return reactions, species, expected


def build(matrix: dict, rhea: dict, xp: dict | None = None, claims: dict | None = None) -> dict:
    reactions, species, columns = checked_matrix(matrix)
    ensure(rhea.get("schema") == "dashi.rhea-chebi-bh4-panel.v2", "unexpected Rhea receipt schema")
    source_reactions = {r.get("rhea_id"): r for r in rhea.get("reactions", [])}
    ensure(all(rid in source_reactions and source_reactions[rid].get("formula_charge_ready")
               for rid in reactions), "finite reaction lacks formula/charge-ready Rhea receipt")
    for rid in reactions:
        source_entries = {}
        for participant in source_reactions[rid].get("participants", []):
            key = str(participant.get("chebi_id") or participant.get("compound_uri")
                      or participant.get("name") or "unidentified")
            ensure(key != "unidentified", "finite reaction participant lacks identity")
            coeff = participant.get("coefficient", 1)
            try:
                coeff = int(str(coeff))
            except (TypeError, ValueError) as exc:
                raise ValueError("invalid source stoichiometry") from exc
            ensure(coeff >= 0, "negative source stoichiometry")
            ensure(participant.get("side") in ("substrate", "product"), "invalid source side")
            sign = -1 if participant["side"] == "substrate" else 1
            source_entries[key] = source_entries.get(key, 0) + sign * coeff
        net_source = {k: v for k, v in source_entries.items() if v}
        net_matrix = {p["species"]: p["signed_coefficient"] for p in columns[rid]}
        ensure(net_source == net_matrix,
               "Rhea participant receipt disagrees with matrix column: " + rid)
    ensure(not matrix.get("external_exchange"), "external exchange must not enter internal S")
    result = {
        "schema": SCHEMA,
        "model_kind": "partial-source-curated-biochemistry-plus-separate-author-hypotheses",
        "authority": AUTHORITY,
        "source_releases": {
            "rhea": rhea.get("rhea_release_reference") or rhea.get("schema"),
            "source_certificate": rhea.get("source_uniprot_panel"),
            "matrix": matrix.get("schema"),
        },
        "species": [{"coordinate": species_coordinate(s), "compartment": None,
                     "external_exchange_interval": None} for s in species],
        "reactions": [
            {"coordinate": coordinate("rhea", rid), "participants": [
                {"coordinate": species_coordinate(e["species"]),
                 "role": "reactant" if e["signed_coefficient"] < 0 else "product",
                 "stoichiometry": abs(e["signed_coefficient"])}
                for e in columns[rid]
            ], "source_owner": "Rhea/ChEBI", "source_receipt": source_reactions[rid].get("participant_sparql_response_sha256"),
             "compartment": None, "physiological_direction_paid": False,
             "rate_law": None, "flux_interval": None, "same_object_payment": False}
            for rid in reactions
        ],
        "excluded_nonfinite_reactions": matrix.get("finite_formula_residuals", []),
        "external_edges": [],
        "ontology_cross_references": [],
        "unparsed_external_annotation_fields": [],
        "author_hypothesis_edges": [],
        "unresolved_external_ontology_targets": [
            "Reactome", "GO/GO-CAM with ECO", "BioPAX Level 3",
            "SBML Level 3 Core with source-paid compartment/rate data",
            "SBO", "WikiPathways", "UBERON/GO cellular component",
        ],
        "remaining_quantitative_coordinates": {
            "reaction_flux": ["REACTION_FLUX:" + rid for rid in reactions],
            "external_exchange": ["EXCHANGE:" + s for s in species],
        },
        "promotion_boundary": {
            "rhea_reaction_is_in_vivo_direction": False,
            "shared_chebi_id_is_same_compartment_pool": False,
            "ontology_match_pays_flux": False,
            "external_annotation_is_author_causal_claim": False,
            "hypothesis_is_experimental_observation": False,
            "structural_jsonld_is_executable_sbml": False,
            "missing_flux_is_zero": False,
            "entire_kitzerow_model_confirmed": False,
        },
    }
    # Source-displayed KEGG/MetaCyc fields are preserved as raw review inputs.
    # A stable external target identity is not invented from an unparsed field.
    # Rhea owns the cross-resource link. In particular, Rhea-to-Reactome
    # mappings do NOT establish the same human/tissue/compartment event.
    for rid in reactions:
        row = source_reactions[rid].get("row") or {}
        for field, namespace, matcher in (
            ("Gene Ontology", "go", GO_IN_TEXT),
            ("Cross-reference (Reactome)", "reactome", REACTOME_IN_TEXT),
        ):
            raw = str(row.get(field) or "").strip()
            matches = sorted(set(matcher.findall(raw)))
            if raw and not matches:
                result["unparsed_external_annotation_fields"].append(
                    {"rhea_id": rid, "source_field": field, "source_value": raw})
            for term in matches:
                result["ontology_cross_references"].append({
                    "reaction": coordinate("rhea", rid),
                    "target": coordinate(namespace, term),
                    "relation": "Rhea-displayed-cross-reference",
                    "source_owner": "Rhea curated/mapped cross-resource table",
                    "source_field": field, "source_value": raw,
                    "source_revision": rhea.get("rhea_release_reference") or rhea.get("schema"),
                    "source_receipt": source_reactions[rid].get("raw_sha256"),
                    "same_biological_event_verified": False,
                    "biological_context_paid": False, "flux_paid": False,
                })
    for rid in reactions:
        row = source_reactions[rid].get("row") or {}
        for field in ("Cross-reference (KEGG)", "Cross-reference (MetaCyc)"):
            raw = str(row.get(field) or "").strip()
            if raw:
                result["unparsed_external_annotation_fields"].append({
                    "rhea_id": rid, "source_field": field, "source_value": raw,
                    "reason": "await-typed-source-revision-mapping-adjudication",
                })
    result["unparsed_external_annotation_fields"].sort(
        key=lambda x: (x["rhea_id"], x["source_field"], x["source_value"]))
    result["ontology_cross_references"].sort(
        key=lambda x: (x["reaction"]["identifier"], x["target"]["namespace"],
                       x["target"]["identifier"]))

    if xp:
        ensure(xp.get("schema") == "dashi.bh4-xpollenation.v1", "unexpected xPollenation schema")
        neighbourhoods = xp.get("neighbourhoods", [])
        found = [n.get("subject", {}).get("identifier") for n in neighbourhoods]
        ensure(len(found) == len(reactions) and set(found) == set(reactions),
               "xPollenation and finite reaction set differ")
        for neighbourhood in neighbourhoods:
            ensure(neighbourhood.get("authority") == "navigation-enrichment-only"
                   and neighbourhood.get("establishesProof") is False
                   and neighbourhood.get("establishesPayment") is False,
                   "xPollenation promotion prohibited")
            for edge in neighbourhood.get("edges", []):
                ensure(edge.get("promotionAllowed") is False
                       and bool(edge.get("sourceRef")) and bool(edge.get("acquisitionReceipt")),
                       "missing edge provenance or promoted ontology edge")
                subject = edge.get("subject") or {}
                obj = edge.get("object") or {}
                ensure(bool(subject.get("namespace") and subject.get("identifier")
                            and obj.get("namespace") and obj.get("identifier")),
                       "malformed external edge")
                ensure(bool(edge.get("edgeId")), "xPollenation edge lacks stable identity")
                if edge.get("relation") == "reaction-participant":
                    rid = neighbourhood["subject"]["identifier"]
                    expected_participants = {p["chebi_id"] for p in
                        source_reactions[rid].get("participants", [])}
                    ensure(subject == neighbourhood["subject"]
                           and obj.get("namespace") == "chebi"
                           and obj.get("identifier") in expected_participants,
                           "participant link contradicts acquired Rhea receipt")
                result["external_edges"].append({
                    "edge_id": edge.get("edgeId"), "subject": coordinate(subject["namespace"], subject["identifier"]),
                    "relation": edge.get("relation"), "object": coordinate(obj["namespace"], obj["identifier"]),
                    "source_ref": edge["sourceRef"], "source_revision": edge.get("sourceRevision"),
                    "acquisition_receipt": edge["acquisitionReceipt"],
                    "status": edge.get("status"), "same_object_verified_upstream": edge.get("sameObjectVerified") is True,
                    "promotion_allowed": False,
                })
        result["external_edges"].sort(key=lambda e: (e["subject"]["namespace"],
            e["subject"]["identifier"], str(e["relation"]), e["object"]["namespace"], e["object"]["identifier"], str(e["edge_id"])))
    if claims:
        ensure(claims.get("schema") == CLAIM_SCHEMA, "unexpected author claim schema")
        for row in claims.get("claims", []):
            ensure(row.get("source_id") in SOURCE_IDS and bool(row.get("source_locator"))
                   and bool(row.get("repo_reconstruction_owner")),
                   "unattributed Kitzerow proposal")
            ensure(row.get("status") == "source-reconstruction-candidate"
                   and row.get("independent_primary_text_verification") is False,
                   "unpaid creator hypothesis promotion")
            ensure(bool(row.get("subject") and row.get("predicate") and row.get("object")),
                   "incomplete hypothesis edge")
            result["author_hypothesis_edges"].append(dict(row))
        result["author_hypothesis_edges"].sort(key=lambda e: (e["source_id"], e["subject"], e["predicate"], e["object"]))
    return result


def jsonld(model: dict) -> dict:
    """RDF-loadable discovery graph. No owl:sameAs and no causal promotion."""
    context = {"dashi": "https://github.com/chboishabba/dashi_agda#",
               "prov": "http://www.w3.org/ns/prov#"}
    graph = []
    for reaction in model["reactions"]:
        rid = reaction["coordinate"]["identifier"]
        node = {"@id": reaction["coordinate"]["uri"], "@type": "dashi:EvidenceIndexedReaction",
                "dashi:sourceOwner": reaction["source_owner"],
                "dashi:compartmentUnresolved": True, "dashi:fluxUnresolved": True,
                "dashi:participants": []}
        for p in reaction["participants"]:
            node["dashi:participants"].append({
                "@type": "dashi:StoichiometricParticipation",
                "dashi:entity": ({"@id": p["coordinate"]["uri"]}
                    if p["coordinate"]["uri"] else
                    {"dashi:sourceIdentifier": p["coordinate"]["identifier"],
                     "dashi:sourceNamespace": p["coordinate"]["namespace"]}),
                "dashi:role": p["role"], "dashi:stoichiometry": p["stoichiometry"]})
        graph.append(node)
    for edge in model["external_edges"]:
        graph.append({"@id": "urn:dashi:bh4:edge:" + str(edge["edge_id"]),
                      "@type": "dashi:UnpromotedEvidenceLink",
                      "dashi:subject": {"@id": edge["subject"]["uri"]} if edge["subject"]["uri"] else edge["subject"],
                      "dashi:relation": edge["relation"],
                      "dashi:object": {"@id": edge["object"]["uri"]} if edge["object"]["uri"] else edge["object"],
                      "dashi:sourceReference": edge["source_ref"],
                      "dashi:acquisitionReceipt": edge["acquisition_receipt"],
                      "dashi:promotionAllowed": False})
    for xref in model["ontology_cross_references"]:
        graph.append({"@id": "urn:dashi:bh4:rhea-xref:" +
                      xref["reaction"]["identifier"].split(":")[1] + ":" +
                      xref["target"]["namespace"] + ":" + xref["target"]["identifier"],
                      "@type": "dashi:UnpromotedRheaCrossReference",
                      "dashi:subject": {"@id": xref["reaction"]["uri"]},
                      "dashi:object": {"@id": xref["target"]["uri"]},
                      "dashi:sourceOwner": xref["source_owner"],
                      "dashi:sourceRevision": xref["source_revision"],
                      "dashi:sourceReceipt": xref["source_receipt"],
                      "dashi:sameBiologicalEventVerified": False})
    for i, row in enumerate(model["author_hypothesis_edges"]):
        graph.append({"@id": "urn:dashi:bh4:kitzerow-hypothesis:" + str(i),
                      "@type": "dashi:UnverifiedAuthorHypothesisReconstruction",
                      "dashi:subjectLabel": row["subject"], "dashi:relation": row["predicate"],
                      "dashi:objectLabel": row["object"], "dashi:sourceId": row["source_id"],
                      "dashi:sourceLocator": row["source_locator"],
                      "dashi:attributionReviewRequired": True})
    return {"@context": context, "@graph": graph}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--matrix", type=Path, required=True)
    ap.add_argument("--rhea", type=Path, required=True)
    ap.add_argument("--xpollenation", type=Path)
    ap.add_argument("--claims", type=Path)
    ap.add_argument("-o", "--output", type=Path, required=True)
    ap.add_argument("--jsonld-output", type=Path)
    args = ap.parse_args()
    result = build(read(args.matrix), read(args.rhea), read(args.xpollenation), read(args.claims))
    for path, payload in [(args.output, result),
                          (args.jsonld_output, jsonld(result))] if args.jsonld_output else [(args.output, result)]:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
